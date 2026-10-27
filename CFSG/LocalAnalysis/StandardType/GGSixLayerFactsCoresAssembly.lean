module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresOrbit

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

variable {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)] {d : Fin r → ℕ}
  {τ : PiMat D d → PiMat D d} {π : Fin r → Fin r}

theorem ggDer_antitone {G : Type*} [Group G] (U : Subgroup G) {m n : ℕ} (h : m ≤ n) :
    LayerFacts.ggDer U n ≤ LayerFacts.ggDer U m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [LayerFacts.ggDer_succ]
    exact (Subgroup.commutator_le.mpr fun x hx y hy =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
        (Subgroup.inv_mem _ hy)).trans ih

variable [∀ i, NeZero (d i)]

variable (π) in
@[expose] noncomputable def factorGroup (hτ : IsInvol τ)
    (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) (b : Fin r) : Subgroup (GL (Fin (d b)) (D b)) :=
  if hb : π b = b then matUnitary (isInvol_tauFix hτ hπ hb) else ⊤

theorem coordHom_mem_factorGroup (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (b : Fin r) {u : (PiMat D d)ˣ} (hu : u ∈ unitaryOf hτ) :
    coordHom D d b u ∈ factorGroup π hτ hπ b := by
  unfold factorGroup
  split_ifs with hb
  · exact coordHom_mem_matUnitary hτ hπ hb hu
  · exact Subgroup.mem_top _

theorem exists_mem_orbitGroup (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (b : Fin r) {g : GL (Fin (d b)) (D b)} (hg : g ∈ factorGroup π hτ hπ b) :
    ∃ s ∈ orbitGroup π hτ b, coordHom D d b s = g := by
  unfold factorGroup at hg
  split_ifs at hg with hb
  · exact exists_mem_orbitGroup_fix hτ hπ hb hg
  · exact exists_mem_orbitGroup_pair hτ hπ hb g

omit [∀ i, NeZero (d i)] in
theorem hasCore_factorGroup (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (hfix : ∀ b (hb : π b = b), HasCore (matUnitary (isInvol_tauFix hτ hπ hb)))
    (hpair : ∀ b, π b ≠ b → HasCore (⊤ : Subgroup (GL (Fin (d b)) (D b)))) (b : Fin r) :
    HasCore (factorGroup π hτ hπ b) := by
  unfold factorGroup
  split_ifs with hb
  · exact hfix b hb
  · exact hpair b hb

theorem eq_of_eq_perm (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i)) {b c : Fin r}
    (hb : b ≤ π b) (hc : c ≤ π c) (h : c = π b) : c = b := by
  have h1 : π c = b := by rw [h, perm_perm hτ hπ]
  exact le_antisymm (h1 ▸ hc) (h ▸ hb)

theorem apply_eq_one_of_mem_orbitGroup (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {b c : Fin r} (hb : b ≤ π b) (hc : c ≤ π c) (hcb : c ≠ b) {s : (PiMat D d)ˣ}
    (hs : s ∈ orbitGroup π hτ b) : (s : PiMat D d) c = 1 :=
  hs.2 c hcb fun h => hcb (eq_of_eq_perm hτ hπ hb hc h)


section CoreOf

variable (π) in
@[expose] def coreOf (hτ : IsInvol τ) (Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))) (b : Fin r) :
    Subgroup (PiMat D d)ˣ :=
  (Sf b).comap (coordHom D d b) ⊓ orbitGroup π hτ b

omit [∀ i, NeZero (d i)] in
theorem coreOf_le (hτ : IsInvol τ) (Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))) (b : Fin r) :
    coreOf π hτ Sf b ≤ unitaryOf hτ :=
  fun _ hs => hs.2.1

theorem conj_mem_coreOf (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))}
    (hSn : ∀ b, ∀ u ∈ factorGroup π hτ hπ b, ∀ s ∈ Sf b, u * s * u⁻¹ ∈ Sf b) {b : Fin r}
    {u s : (PiMat D d)ˣ} (hu : u ∈ unitaryOf hτ) (hs : s ∈ coreOf π hτ Sf b) :
    u * s * u⁻¹ ∈ coreOf π hτ Sf b := by
  obtain ⟨hs1, hs2⟩ := Subgroup.mem_inf.mp hs
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr ?_, conj_mem_orbitGroup hτ hu hs2⟩
  rw [map_mul, map_mul, map_inv]
  exact hSn b _ (coordHom_mem_factorGroup hτ hπ b hu) _ (Subgroup.mem_comap.mp hs1)

theorem bijective_coreOf (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))} (hSle : ∀ b, Sf b ≤ factorGroup π hτ hπ b)
    (b : Fin r) :
    Function.Bijective (((coordHom D d b).comp (coreOf π hτ Sf b).subtype).codRestrict (Sf b)
      fun s => Subgroup.mem_comap.mp (Subgroup.mem_inf.mp s.2).1) := by
  refine ⟨fun s t h => Subtype.ext (coordHom_injOn hτ hπ (Subgroup.mem_inf.mp s.2).2
    (Subgroup.mem_inf.mp t.2).2 (congrArg Subtype.val h)), fun g => ?_⟩
  obtain ⟨s, hs, hsg⟩ := exists_mem_orbitGroup hτ hπ b (hSle b g.2)
  refine ⟨⟨s, Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hsg]; exact g.2), hs⟩⟩,
    Subtype.ext ?_⟩
  exact hsg

theorem mem_iSup_coreOf (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))} (hSle : ∀ b, Sf b ≤ factorGroup π hτ hπ b)
    {u : (PiMat D d)ˣ} (hu : u ∈ unitaryOf hτ)
    (h : ∀ b, b ≤ π b → coordHom D d b u ∈ Sf b) :
    u ∈ ⨆ c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, coreOf π hτ Sf c.1 := by
  classical
  suffices H : ∀ n : ℕ, ∀ u ∈ unitaryOf hτ, (∀ b, b ≤ π b → coordHom D d b u ∈ Sf b) →
      (Finset.univ.filter fun b => b ≤ π b ∧ (u : PiMat D d) b ≠ 1).card ≤ n →
      u ∈ ⨆ c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, coreOf π hτ Sf c.1 from
    H _ u hu h le_rfl
  intro n
  induction n with
  | zero =>
    intro u hu _ hn
    have h1 : u = 1 := eq_one_of_forall_le hτ hπ hu fun b hb => by
      by_contra hne
      have hmem : b ∈ Finset.univ.filter fun b => b ≤ π b ∧ (u : PiMat D d) b ≠ 1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, hne⟩
      have := Finset.card_pos.mpr ⟨b, hmem⟩
      omega
    rw [h1]
    exact Subgroup.one_mem _
  | succ n ih =>
    intro u hu h hn
    by_cases hall : ∀ b, b ≤ π b → (u : PiMat D d) b = 1
    · rw [eq_one_of_forall_le hτ hπ hu hall]
      exact Subgroup.one_mem _
    push Not at hall
    obtain ⟨b, hb, hub⟩ := hall
    have hSb : Sf b ≠ ⊥ := fun hbot => hub (by
      have h1 := h b hb
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : ((coordHom D d b u : GL (Fin (d b)) (D b)) :
          Matrix (Fin (d b)) (Fin (d b)) (D b)) = 1 := by rw [h1, Units.val_one]
      exact h2)
    obtain ⟨s, hs, hsu⟩ := exists_mem_orbitGroup hτ hπ b (hSle b (h b hb))
    have hsS : s ∈ coreOf π hτ Sf b :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hsu]; exact h b hb), hs⟩
    have hu' : s⁻¹ * u ∈ unitaryOf hτ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hs.1) hu
    have hcoord : ∀ c, c ≤ π c → c ≠ b → ((s⁻¹ * u : (PiMat D d)ˣ) : PiMat D d) c =
        (u : PiMat D d) c := by
      intro c hc hcb
      have hsc := apply_eq_one_of_mem_orbitGroup hτ hπ hb hc hcb hs
      have h1 := inv_apply_mul_apply s c
      rw [hsc, Matrix.mul_one] at h1
      rw [Units.val_mul, Pi.mul_apply, h1, Matrix.one_mul]
    have hb' : ((s⁻¹ * u : (PiMat D d)ˣ) : PiMat D d) b = 1 := by
      have h1 : coordHom D d b (s⁻¹ * u) = 1 := by rw [map_mul, map_inv, hsu, inv_mul_cancel]
      have h2 : ((coordHom D d b (s⁻¹ * u) : GL (Fin (d b)) (D b)) :
          Matrix (Fin (d b)) (Fin (d b)) (D b)) = 1 := by rw [h1, Units.val_one]
      exact h2
    have h' : ∀ c, c ≤ π c → coordHom D d c (s⁻¹ * u) ∈ Sf c := by
      intro c hc
      by_cases hcb : c = b
      · subst hcb
        rw [map_mul, map_inv, hsu, inv_mul_cancel]
        exact Subgroup.one_mem _
      · have h1 : coordHom D d c (s⁻¹ * u) = coordHom D d c u := Units.ext (hcoord c hc hcb)
        rw [h1]
        exact h c hc
    have hn' : (Finset.univ.filter fun c => c ≤ π c ∧
        ((s⁻¹ * u : (PiMat D d)ˣ) : PiMat D d) c ≠ 1).card ≤ n := by
      have hlt : (Finset.univ.filter fun c => c ≤ π c ∧
          ((s⁻¹ * u : (PiMat D d)ˣ) : PiMat D d) c ≠ 1) ⊂
          (Finset.univ.filter fun c => c ≤ π c ∧ (u : PiMat D d) c ≠ 1) := by
        refine Finset.ssubset_iff_of_subset (fun c hc => ?_) |>.mpr ⟨b, ?_, ?_⟩
        · rw [Finset.mem_filter] at hc ⊢
          have hcb : c ≠ b := fun h => hc.2.2 (h ▸ hb')
          exact ⟨hc.1, hc.2.1, by rw [← hcoord c hc.2.1 hcb]; exact hc.2.2⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, hub⟩
        · rw [Finset.mem_filter]
          exact fun hc => hc.2.2 hb'
      have := Finset.card_lt_card hlt
      omega
    have hrest := ih _ hu' h' hn'
    have hu_eq : u = s * (s⁻¹ * u) := by rw [mul_inv_cancel_left]
    rw [hu_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem
      (S := fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} => coreOf π hτ Sf c.1)
      (⟨b, hb, hSb⟩ : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}) hsS) hrest

end CoreOf


section Main

theorem exists_ggDer_le_iSup_coreOf (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))} (hSle : ∀ b, Sf b ≤ factorGroup π hτ hπ b)
    (hder : ∀ b, ∃ k, LayerFacts.ggDer (factorGroup π hτ hπ b) k ≤ Sf b) :
    ∃ k, LayerFacts.ggDer (unitaryOf hτ) k ≤
      ⨆ c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, coreOf π hτ Sf c.1 := by
  classical
  choose kf hkf using hder
  refine ⟨Finset.univ.sup kf, fun u hu => ?_⟩
  have huU : u ∈ unitaryOf hτ := ggDer_antitone _ (Nat.zero_le _) hu
  refine mem_iSup_coreOf hτ hπ hSle huU fun b _ => ?_
  have h1 : coordHom D d b u ∈
      LayerFacts.ggDer ((unitaryOf hτ).map (coordHom D d b)) (Finset.univ.sup kf) := by
    rw [← LayerFacts.map_ggDer]
    exact Subgroup.mem_map_of_mem _ hu
  have h2 : (unitaryOf hτ).map (coordHom D d b) ≤ factorGroup π hτ hπ b := by
    rintro _ ⟨v, hv, rfl⟩
    exact coordHom_mem_factorGroup hτ hπ b hv
  exact hkf b (ggDer_antitone _ (Finset.le_sup (Finset.mem_univ b))
    (LayerFacts.ggDer_mono h2 _ h1))

theorem eq_one_of_mem_iSup_coreOf (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {Sf : ∀ b, Subgroup (GL (Fin (d b)) (D b))} (hSle : ∀ b, Sf b ≤ factorGroup π hτ hπ b)
    (hcent : ∀ b, Sf b ≠ ⊥ → ∀ z ∈ Sf b, (∀ y ∈ Sf b, z * y = y * z) → z ^ 2 = 1 → z = 1)
    {z : (PiMat D d)ˣ}
    (hz : z ∈ ⨆ c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, coreOf π hτ Sf c.1)
    (hzc : ∀ y ∈ ⨆ c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, coreOf π hτ Sf c.1, z * y = y * z)
    (hz2 : z ^ 2 = 1) : z = 1 := by
  have hle0 : (⨆ c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, coreOf π hτ Sf c.1) ≤ unitaryOf hτ :=
    iSup_le fun c => coreOf_le hτ Sf c.1
  have hzU : z ∈ unitaryOf hτ := hle0 hz
  refine eq_one_of_forall_le hτ hπ hzU fun b hb => ?_
  have hle : (⨆ c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, coreOf π hτ Sf c.1) ≤
      (Sf b).comap (coordHom D d b) := by
    refine iSup_le fun c => fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := Subgroup.mem_inf.mp hs
    by_cases hcb : c.1 = b
    · rw [← hcb]
      exact hs1
    · have h1 := apply_eq_one_of_mem_orbitGroup hτ hπ c.2.1 hb (Ne.symm hcb) hs2
      have h2 : coordHom D d b s = 1 := Units.ext h1
      rw [Subgroup.mem_comap, h2]
      exact Subgroup.one_mem _
  have hzb : coordHom D d b z ∈ Sf b := hle hz
  have h1 : coordHom D d b z = 1 := by
    by_cases hSb : Sf b = ⊥
    · rw [hSb] at hzb
      exact Subgroup.mem_bot.mp hzb
    · refine hcent b hSb _ hzb (fun y hy => ?_) (by rw [← map_pow, hz2, map_one])
      obtain ⟨s, hs, hsy⟩ := exists_mem_orbitGroup hτ hπ b (hSle b hy)
      have hsS : s ∈ coreOf π hτ Sf b :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr (by rw [hsy]; exact hy), hs⟩
      have h3 := hzc s (Subgroup.mem_iSup_of_mem
        (S := fun c : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥} => coreOf π hτ Sf c.1)
        (⟨b, hb, hSb⟩ : {b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}) hsS)
      rw [← hsy, ← map_mul, ← map_mul, h3]
  have h2 : ((coordHom D d b z : GL (Fin (d b)) (D b)) :
      Matrix (Fin (d b)) (Fin (d b)) (D b)) = 1 := by rw [h1, Units.val_one]
  exact h2

theorem exists_core_of_factors (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    (hfix : ∀ b (hb : π b = b), HasCore (matUnitary (isInvol_tauFix hτ hπ hb)))
    (hpair : ∀ b, π b ≠ b → HasCore (⊤ : Subgroup (GL (Fin (d b)) (D b)))) :
    ∃ (β : Type) (S : β → Subgroup (PiMat D d)ˣ), (∀ c, S c ≤ unitaryOf hτ) ∧
      (∀ c, ∀ u ∈ unitaryOf hτ, ∀ s ∈ S c, u * s * u⁻¹ ∈ S c) ∧
      (∀ c, CFSG.IsQuasisimple (S c)) ∧
      (∃ k, LayerFacts.ggDer (unitaryOf hτ) k ≤ ⨆ c, S c) ∧
      ∀ z ∈ ⨆ c, S c, (∀ y ∈ ⨆ c, S c, z * y = y * z) → z ^ 2 = 1 → z = 1 := by
  choose Sf hSle hSn hder hq using hasCore_factorGroup hτ hπ hfix hpair
  refine ⟨{b : Fin r // b ≤ π b ∧ Sf b ≠ ⊥}, fun c => coreOf π hτ Sf c.1,
    fun c => coreOf_le hτ Sf c.1, fun c u hu s hs => conj_mem_coreOf hτ hπ hSn hu hs,
    fun c => ?_, exists_ggDer_le_iSup_coreOf hτ hπ hSle hder,
    fun z hz hzc hz2 => eq_one_of_mem_iSup_coreOf hτ hπ hSle
      (fun b hb => ((hq b).resolve_left hb).2) hz hzc hz2⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MulEquiv.ofBijective _ (bijective_coreOf hτ hπ hSle c.1)).symm ((hq c.1).resolve_left c.2.2).1

end Main

end LayerCores

end CFSG.StandardType
