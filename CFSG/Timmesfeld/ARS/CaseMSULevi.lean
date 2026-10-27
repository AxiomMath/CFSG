module

public import CFSG.Timmesfeld.ARS.CaseMSU
public import CFSG.Timmesfeld.ARS.CaseMSpLevi
public import Certificates.Certificate15951

public section

namespace CFSG.Timmesfeld.ARS

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Timmesfeld.LieEmbed

namespace CaseMSU

theorem toStd_six (γ : Fin 3 → ℤ) : Unitary.toStd 6 γ = Symplectic.toStd 3 γ := by
  rw [Unitary.toStd, ite_eq_left (show Even 6 from ⟨3, rfl⟩)]

set_option maxRecDepth 100000 in
theorem diff_weight_check : ∀ (a b : Fin 3) (i j : Fin 6), a ≠ b →
    weight 6 i - weight 6 j = Pi.single a 1 - Pi.single b 1 →
    (i.val < 3 ↔ j.val < 3) ∧ ∀ t : Fin 3, t ≠ a → t ≠ b →
      j ≠ c6 t ∧ j ≠ c6' t ∧ Fin.rev i ≠ c6 t ∧ Fin.rev i ≠ c6' t :=
  Certificates.certificate15951.1

set_option maxRecDepth 100000 in
theorem two_weight_ne_diff : ∀ (a b : Fin 3) (i : Fin 6), a ≠ b →
    2 • weight 6 i ≠ Pi.single a 1 - Pi.single b 1 :=
  Certificates.certificate15951.2

theorem exists_third : ∀ a b : Fin 3, a ≠ b → ∃ t : Fin 3, t ≠ a ∧ t ≠ b := by decide

theorem rev_c6 : ∀ k : Fin 3, Fin.rev (c6 k) = c6' k := by decide

theorem rev_c6' : ∀ k : Fin 3, Fin.rev (c6' k) = c6 k := by decide

section Vectors

variable {F : Type*} [Field F] (σ : F ≃+* F)

theorem uForm_of_low_eq_zero {v w : Fin 6 → F} (hv : ∀ x : Fin 6, x.val < 3 → v x = 0)
    (hw : ∀ x : Fin 6, x.val < 3 → w x = 0) : uForm σ v w = 0 := by
  rw [uForm_eq]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x.val < 3
  · rw [hv x hx, map_zero, zero_mul]
  · rw [hw (Fin.rev x) (by rw [Fin.val_rev]; omega), mul_zero]

theorem uForm_of_high_eq_zero {v w : Fin 6 → F} (hv : ∀ x : Fin 6, 3 ≤ x.val → v x = 0)
    (hw : ∀ x : Fin 6, 3 ≤ x.val → w x = 0) : uForm σ v w = 0 := by
  rw [uForm_eq]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : 3 ≤ x.val
  · rw [hv x hx, map_zero, zero_mul]
  · rw [hw (Fin.rev x) (by rw [Fin.val_rev]; omega), mul_zero]

theorem rootMatrix_mulVec_low {i j : Fin 6} (hij : i.val < 3 ↔ j.val < 3) (c : F)
    {v : Fin 6 → F} (hv : ∀ x : Fin 6, x.val < 3 → v x = 0) (x : Fin 6) (hx : x.val < 3) :
    (rootMatrix σ i j c *ᵥ v) x = 0 := by
  rw [rootMatrix_mulVec_apply, hv x hx]
  have e1 : (if x = i then c * v j else 0) = 0 := by
    split_ifs with h
    · rw [hv j (hij.1 (h ▸ hx)), mul_zero]
    · rfl
  have e2 : (if x = Fin.rev j then σ c * v (Fin.rev i) else 0) = 0 := by
    split_ifs with h
    · have h' : (Fin.rev j).val < 3 := h ▸ hx
      rw [Fin.val_rev] at h'
      have hj : ¬ j.val < 3 := by omega
      have hi : ¬ i.val < 3 := fun hi => hj (hij.1 hi)
      rw [hv (Fin.rev i) (by rw [Fin.val_rev]; omega), mul_zero]
    · rfl
  rw [e1, e2, zero_add, sub_zero]

theorem rootMatrix_mulVec_high {i j : Fin 6} (hij : i.val < 3 ↔ j.val < 3) (c : F)
    {v : Fin 6 → F} (hv : ∀ x : Fin 6, 3 ≤ x.val → v x = 0) (x : Fin 6) (hx : 3 ≤ x.val) :
    (rootMatrix σ i j c *ᵥ v) x = 0 := by
  rw [rootMatrix_mulVec_apply, hv x hx]
  have e1 : (if x = i then c * v j else 0) = 0 := by
    split_ifs with h
    · have hi : ¬ i.val < 3 := by rw [← h]; omega
      have hj : ¬ j.val < 3 := fun hj => hi (hij.2 hj)
      rw [hv j (by omega), mul_zero]
    · rfl
  have e2 : (if x = Fin.rev j then σ c * v (Fin.rev i) else 0) = 0 := by
    split_ifs with h
    · have h' : 3 ≤ (Fin.rev j).val := h ▸ hx
      rw [Fin.val_rev] at h'
      have hi : i.val < 3 := hij.2 (by omega)
      rw [hv (Fin.rev i) (by rw [Fin.val_rev]; omega), mul_zero]
    · rfl
  rw [e1, e2, zero_add, sub_zero]

end Vectors

end CaseMSU

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem conjSub_eq_of_preserves_su (hF : Nat.card F = (p ^ f) ^ 2)
    (Φ : SU (unitaryInvolution F p f) 6 →* G) (hker : Φ.ker ≤ Subgroup.center _)
    (hrange : Φ.range = levi R A A₀)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔ ∃ g, X = (conjSub (Unitary.rootGroup
      (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6 (Pi.single (2 : Fin 3) 1))
        g).map Φ)
    {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) {u : Fin 3 → Fin 6 → F}
    {Y : Fin 3 → Subgroup (SU (unitaryInvolution F p f) 6)}
    (hY : ∀ k, IsUTransGroup (unitaryInvolution F p f) (u k) (Y k))
    (huu : ∀ k, uForm (unitaryInvolution F p f) (u k) (u k) = 0)
    (hYB : ∀ k, (Y k).map Φ ∈ deltaSet R A A₀ B) (W : (Fin 6 → F) → Prop)
    (hWu : ∀ v, (∀ k, uForm (unitaryInvolution F p f) v (u k) = 0) → W v)
    (hWsmul : ∀ k (c : F), W (c • u k))
    (hWform : ∀ v w, W v → W w → uForm (unitaryInvolution F p f) v w = 0)
    {s : SU (unitaryInvolution F p f) 6} (hs2 : s * s = 1)
    (hsW : ∀ v, W v → W (suMat _ 6 s *ᵥ v)) : conjSub B (Φ s) = B := by
  have hσ : ∀ c, unitaryInvolution F p f (unitaryInvolution F p f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hζ' : (ζ : F) + unitaryInvolution F p f ζ = 0 := ζ.2
  have hR := hS.hyp.root
  have hz : Φ s ∈ levi R A A₀ := hrange ▸ ⟨s, rfl⟩
  have hz2 : Φ s * Φ s = 1 := by rw [← map_mul, hs2, map_one]
  have hvec : ∀ {X : Subgroup G}, X ∈ deltaSet R A A₀ B → ∀ {g : SU (unitaryInvolution F p f) 6},
      X = (conjSub (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF)
        6 (Pi.single (2 : Fin 3) 1)) g).map Φ →
      ∀ {v : Fin 6 → F}, v ≠ 0 → uForm (unitaryInvolution F p f) v v = 0 →
      IsUTransGroup (unitaryInvolution F p f) v (conjSub (Unitary.rootGroup
        (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6 (Pi.single (2 : Fin 3) 1))
          g) → W v := by
    intro X hX g hXg v hv hvv hvT
    by_cases hall : ∀ k, uForm (unitaryInvolution F p f) v (u k) = 0
    · exact hWu v hall
    push Not at hall
    obtain ⟨k, hk⟩ := hall
    have hc : Commuting X ((Y k).map Φ) := hS.commuting_of_mem_deltaSet' hB hX (hYB k)
    rw [hXg] at hc
    rcases hvT.uForm_eq_zero_of_center hσ hζ hζ' (hY k) hv hvv (huu k)
        (CaseMSU.commutator_mem_center hker hc) with h0 | ⟨l, hl⟩
    · exact absurd h0 hk
    · have hl0 : l ≠ 0 := fun h0 => by
        rw [h0, zero_smul] at hl
        rw [hl] at hk
        exact hk (by simp [uForm])
      have : v = l⁻¹ • u k := by rw [hl, smul_smul, inv_mul_cancel₀ hl0, one_smul]
      rw [this]
      exact hWsmul k l⁻¹
  refine hS.conjSub_eq_of_deltaSet_subset hB hz hz2 fun X hX => ?_
  obtain ⟨g, hXg⟩ := (hΔ X).1 hX.1
  obtain ⟨v, hv0, hvv, hvT⟩ := CaseMSU.exists_isUTransGroup_of_mem hF g
  have hWv := hvec hX hXg hv0 hvv hvT
  have hXz : conjSub X (Φ s) = (conjSub (conjSub (Unitary.rootGroup (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) 6 (Pi.single (2 : Fin 3) 1)) g) s).map Φ := by
    rw [hXg, map_conjSub_eq]
  have hzT := hvT.conjSub s
  refine hS.mem_deltaSet_of_forall_commuting hB
    (Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hz) fun Y' hY' => ?_
  obtain ⟨g', hY'g⟩ := (hΔ Y').1 hY'.1
  obtain ⟨w, hw0, hww, hwT⟩ := CaseMSU.exists_isUTransGroup_of_mem hF g'
  have hWw := hvec hY' hY'g hw0 hww hwT
  rw [hXz, hY'g]
  exact CaseMSU.commuting_map Φ (hzT.commuting hσ hwT (hWform _ _ (hsW v hWv) hWw))

theorem commuting_diffRoot_su_of_card {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (Φ : SU (unitaryInvolution F 2 f) 6 →* G) (hker : Φ.ker ≤ Subgroup.center _)
    (hrange : Φ.range = levi R A A₀)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔ ∃ g, X = (conjSub (Unitary.rootGroup
      (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 6 (Pi.single (2 : Fin 3) 1))
        g).map Φ)
    (hP : ∀ i, (Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 6
      (CaseM.longC3 i)).map Φ = P i)
    (hQ : ∀ i, (Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 6
      (-CaseM.longC3 i)).map Φ = Q i)
    {a b : Fin 3} (hab : a ≠ b) {γ : Fin 3 → ℤ}
    (hγ : Symplectic.toStd 3 γ = Pi.single a 1 - Pi.single b 1) :
    Commuting ((Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 6
      γ).map Φ) E ∧
    Commuting ((Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 6
      γ).map Φ) ⁅A₀, C⁆ := by
  have hA := hS.mem
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have hγ' : Unitary.toStd 6 γ = Pi.single a 1 - Pi.single b 1 := (CaseMSU.toStd_six γ).trans hγ
  obtain ⟨t, hta, htb⟩ := CaseMSU.exists_third a b hab
  have hS₀ : Sec12 R A₀ A := hS.of_mem_omegaSet hS.opp.1 ⟨hA, hS.opp.2.symm⟩
  have hlevi : leviSet R A₀ A = leviSet R A A₀ := Set.inter_comm _ _
  have hlevi' : levi R A₀ A = levi R A A₀ := by simp only [levi, hlevi]
  obtain ⟨hFm, -, -, hYF⟩ := CaseD4.commutator_props hS.hyp hA hS.opp hfr.memC
  have hPF : ∀ k, Commuting (P k) ⁅A₀, C⁆ := fun k =>
    hYF (P k) (hfr.memP k).1 (hfr.memP k).2.1.2.2.symm
  have key : ∀ (i j : Fin 6) (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j),
      weight 6 i - weight 6 j = Pi.single a 1 - Pi.single b 1 → ∀ c,
        (∀ e ∈ E, Commute (Φ (rootHom _ hσ hij hi hj c)) e) ∧
        (∀ e ∈ ⁅A₀, C⁆, Commute (Φ (rootHom _ hσ hij hi hj c)) e) := by
    intro i j hij hi hj hw c
    obtain ⟨hside, hfix⟩ := CaseMSU.diff_weight_check a b i j hab hw
    obtain ⟨hj1, hj2, hi1, hi2⟩ := hfix t hta htb
    have hmat : suMat _ 6 (rootHom _ hσ hij hi hj c) =
        rootMatrix (unitaryInvolution F 2 f) i j c.toAdd := rfl
    have hs2 : rootHom _ hσ hij hi hj c * rootHom _ hσ hij hi hj c = 1 := by
      have hc : c * c = 1 := Multiplicative.toAdd.injective (by
        rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero])
      rw [← map_mul, hc, map_one]
    have hz2 : Φ (rootHom _ hσ hij hi hj c) * Φ (rootHom _ hσ hij hi hj c) = 1 := by
      rw [← map_mul, hs2, map_one]
    have hzP : ∀ x ∈ P t, Commute (Φ (rootHom _ hσ hij hi hj c)) x := by
      intro x hx
      rw [← hP t] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (((CaseMSU.isUTransGroup_pos hF t).commute_of_mulVec_eq (by
        rw [hmat]; exact rootMatrix_mulVec_single hj1 hi1 _)) y hy).map Φ
    have hzQ : ∀ x ∈ Q t, Commute (Φ (rootHom _ hσ hij hi hj c)) x := by
      intro x hx
      rw [← hQ t] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (((CaseMSU.isUTransGroup_neg hF t).commute_of_mulVec_eq (by
        rw [hmat]; exact rootMatrix_mulVec_single hj2 hi2 _)) y hy).map Φ
    constructor
    ·
      have hzE : conjSub E (Φ (rootHom _ hσ hij hi hj c)) = E :=
        hS.conjSub_eq_of_preserves_su hF Φ hker hrange hΔ hfr.memE
          (u := fun k => Pi.single (c6' k) 1)
          (Y := fun k => Unitary.rootGroup (unitaryInvolution F 2 f)
            (unitaryInvolution_involutive hF) 6 (-CaseM.longC3 k))
          (CaseMSU.isUTransGroup_neg hF) (fun k => uForm_single_self (CaseMSU.c6'_ne_rev k))
          (fun k => by rw [hQ k]; exact hfr.memQ k) (fun v => ∀ x : Fin 6, x.val < 3 → v x = 0)
          (fun v hv x hx => by
            have h1 := hv ⟨x.val, hx⟩
            simp only [uForm_single_right, CaseMSU.rev_c6', map_eq_zero] at h1
            exact h1)
          (fun k c' x hx => by
            have hne : x ≠ c6' k := fun h => by
              have h' : x.val = 5 - k.val := congrArg Fin.val h
              omega
            simp [hne])
          (fun v w hv hw => CaseMSU.uForm_of_low_eq_zero _ hv hw) hs2
          (fun v hv x hx => by rw [hmat]; exact CaseMSU.rootMatrix_mulVec_low _ hside _ hv x hx)
      exact hS.commute_of_conjSub_eq_of_pair hfr.memE (hfr.memP t).1 (hfr.memQ t).1
        (hfr.opposite t) (hfr.memQ t).2.1.2.2.symm hzE hzP hzQ hz2
    ·
      have hzF : conjSub ⁅A₀, C⁆ (Φ (rootHom _ hσ hij hi hj c)) = ⁅A₀, C⁆ :=
        hS₀.conjSub_eq_of_preserves_su hF Φ hker (hrange.trans hlevi'.symm)
          (fun X => by rw [hlevi]; exact hΔ X) hFm (u := fun k => Pi.single (c6 k) 1)
          (Y := fun k => Unitary.rootGroup (unitaryInvolution F 2 f)
            (unitaryInvolution_involutive hF) 6 (CaseM.longC3 k))
          (CaseMSU.isUTransGroup_pos hF) (fun k => uForm_single_self (CaseMSU.c6_ne_rev k))
          (fun k => by
            rw [hP k]
            exact hS₀.mem_deltaSet_of_commuting hFm (hlevi ▸ (hfr.memP k).1) (hPF k).symm)
          (fun v => ∀ x : Fin 6, 3 ≤ x.val → v x = 0)
          (fun v hv x hx => by
            have h1 := hv ⟨5 - x.val, by omega⟩
            simp only [uForm_single_right, CaseMSU.rev_c6, map_eq_zero] at h1
            have h2 : c6' ⟨5 - x.val, by omega⟩ = x := Fin.ext (show 5 - (5 - x.val) = x.val by
              omega)
            rwa [h2] at h1)
          (fun k c' x hx => by
            have hne : x ≠ c6 k := fun h => by
              have h' : x.val = k.val := congrArg Fin.val h
              omega
            simp [hne])
          (fun v w hv hw => CaseMSU.uForm_of_high_eq_zero _ hv hw) hs2
          (fun v hv x hx => by rw [hmat]; exact CaseMSU.rootMatrix_mulVec_high _ hside _ hv x hx)
      exact hS₀.commute_of_conjSub_eq_of_pair hFm (hlevi ▸ (hfr.memQ t).1)
        (hlevi ▸ (hfr.memP t).1) (hfr.opposite t).symm (hPF t) hzF hzQ hzP hz2
  have hext : ∀ B : Subgroup G, (∀ (i j : Fin 6) (hij : i ≠ j) (hi : i ≠ Fin.rev i)
      (hj : j ≠ Fin.rev j), weight 6 i - weight 6 j = Pi.single a 1 - Pi.single b 1 → ∀ c,
        ∀ e ∈ B, Commute (Φ (rootHom _ hσ hij hi hj c)) e) →
      Commuting ((Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
        6 γ).map Φ) B := by
    intro B hB
    have hle : Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 6 γ ≤
        (Subgroup.centralizer (B : Set G)).comap Φ := by
      refine sup_le (sup_le ?_ ?_) ?_
      · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi =>
          iSup_le fun hj => iSup_le fun _ => iSup_le fun hw => ?_
        rintro _ ⟨c, rfl⟩
        exact Subgroup.mem_comap.2 (Subgroup.mem_centralizer_iff.2 fun e he =>
          (hB i j hij hi hj (hw.trans hγ') c e he).eq.symm)
      · exact iSup_le fun i => iSup_le fun _ => iSup_le fun hw =>
          absurd (hw.trans hγ') (CaseMSU.two_weight_ne_diff a b i hab)
      · exact iSup_le fun _ => iSup_le fun k => iSup_le fun _ => iSup_le fun _ =>
          iSup_le fun hk => absurd hk (rev_ne_self_six' k)
    rintro _ ⟨x, hx, rfl⟩ e he
    exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) e he).symm
  exact ⟨hext E fun i j hij hi hj hw c => (key i j hij hi hj hw c).1,
    hext _ fun i j hij hi hj hw c => (key i j hij hi hj hw c).2⟩

theorem commuting_diffRoot_su {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) {f : ℕ} (hf : 1 ≤ f)
    (Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →* G)
    (hker : Φ.ker ≤ Subgroup.center _) (hrange : Φ.range = levi R A A₀)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔ ∃ g, X = (conjSub
      ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
        (Pi.single (2 : Fin 3) 1)) g).map Φ)
    (hP : ∀ i, ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
      (CaseM.longC3 i)).map Φ = P i)
    (hQ : ∀ i, ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
      (-CaseM.longC3 i)).map Φ = Q i)
    {a b : Fin 3} (hab : a ≠ b) {γ : Fin 3 → ℤ}
    (hγ : Symplectic.toStd 3 γ = Pi.single a 1 - Pi.single b 1) :
    Commuting (((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup γ).map Φ)
      E ∧
    Commuting (((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup γ).map Φ)
      ⁅A₀, C⁆ :=
  hS.commuting_diffRoot_su_of_card hfr (CaseM.card_galoisField_two_mul hf) Φ hker hrange hΔ hP
    hQ hab hγ

end Sec12

end CFSG.Timmesfeld.ARS
