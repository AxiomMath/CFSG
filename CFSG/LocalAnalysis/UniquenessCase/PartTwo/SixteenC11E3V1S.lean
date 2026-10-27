module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Ctx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Om4Fpf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1611e3_commSub_top_of_sumOfNat_two {W : Type} [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    (h : SumOfNat N H ⊤ ⊥ 2) (hirr : ∀ I : Subgroup W, N H I ⊥ → I ∈ irrSet H) :
    commSub ⊤ H = ⊤ := by
  obtain ⟨J₀, J₁, hN₀, hN₁, -, hsup⟩ := s16c167_sumOfNat_two h
  have hc₀ : commSub J₀ H = J₀ := (hirr J₀ hN₀).1
  have hc₁ : commSub J₁ H = J₁ := (hirr J₁ hN₁).1
  have hsub : J₀ ⊔ J₁ ≤ commSub ⊤ H :=
    sup_le (by rw [← hc₀]; exact commSub_mono le_top le_rfl)
      (by rw [← hc₁]; exact commSub_mono le_top le_rfl)
  exact le_antisymm le_top (hsup ▸ hsub)

private theorem s1611e3_exists_zpow_mul_zpow_of_mem_sup {A : Type} [Group A] {b d x : A}
    (hbd : Commute b d) (hx : x ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d) :
    ∃ i j : ℤ, x = b ^ i * d ^ j := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨i, 0, by rw [zpow_zero, mul_one]⟩
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨0, j, by rw [zpow_zero, one_mul]⟩
  | one => exact ⟨0, 0, by rw [zpow_zero, zpow_zero, mul_one]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨i, j, rfl⟩ := ihx
    obtain ⟨k, l, rfl⟩ := ihy
    refine ⟨i + k, j + l, ?_⟩
    calc b ^ i * d ^ j * (b ^ k * d ^ l) = b ^ i * (d ^ j * b ^ k) * d ^ l := by
          simp only [mul_assoc]
      _ = b ^ i * (b ^ k * d ^ j) * d ^ l := by rw [(hbd.symm.zpow_zpow j k).eq]
      _ = b ^ (i + k) * d ^ (j + l) := by rw [zpow_add, zpow_add]; simp only [mul_assoc]
  | inv x _ ih =>
    obtain ⟨i, j, rfl⟩ := ih
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (hbd.symm.zpow_zpow (-j) (-i)).eq

theorem s1611e3_s15_eq_one_of_commStar {D : Data G} (h1217 : R1217 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hcomm : commSub (⊤ : Subgroup (vStar D.M ⊥ V hV L)) (lStar D.M ⊥ V hV L) = ⊤) :
    s15 D.M ⊥ V hV L = 1 := by
  let κ : Vtil ⊥ V hV →* vStar D.M ⊥ V hV L :=
    s15T7Kappa ⊥ (v1Sub D.M ⊥ V hV L) V hV (s15_Infra_le_v1Sub D.M ⊥ V hV L)
  obtain ⟨ρ, -, hρκ⟩ := s16e_two_kappa_equiv D h1217 hc.setting.hyp151 hV
  have hkey : ∀ φ ∈ Mbar D.M ⊥ V hV,
      (barSub ⊥ V hV L).map (MulAut.conj φ).toMonoidHom = barSub ⊥ V hV L := by
    intro φ hφ
    by_contra hne
    obtain ⟨g, hgM, hgφ⟩ := (mem_barSub ⊥ V hV D.M φ).1 hφ
    set g₀ : G := (g : G) with hg₀
    have hg0M : g₀ ∈ D.M := hgM
    have hiff : ((barSub ⊥ V hV L).map (MulAut.conj φ).toMonoidHom = barSub ⊥ V hV L) ↔
        ((barSub ⊥ V hV L).map (MulAut.conj φ⁻¹).toMonoidHom = barSub ⊥ V hV L) := by
      simp only [MulEquiv.toMonoidHom_eq_coe]
      rw [← Subgroup.mem_normalizer_iff_map_conj_eq (H := barSub ⊥ V hV L) (g := φ),
        ← Subgroup.mem_normalizer_iff_map_conj_eq (H := barSub ⊥ V hV L) (g := φ⁻¹)]
      exact (Subgroup.inv_mem_iff (Subgroup.normalizer (barSub ⊥ V hV L :
        Set (MulAut (Vtil ⊥ V hV))))).symm
    have hL'eq : barSub ⊥ V hV (conjSubgroup L g₀) =
        (barSub ⊥ V hV L).map (MulAut.conj φ⁻¹).toMonoidHom := by
      rw [s15_Infra_barSub_conjSubgroup ⊥ V hV g.2 L, hgφ]
    have hL'ne : barSub ⊥ V hV (conjSubgroup L g₀) ≠ barSub ⊥ V hV L := by
      rw [hL'eq]
      exact fun h => hne (hiff.mpr h)
    have hL'ne_bot : barSub ⊥ V hV (conjSubgroup L g₀) ≠ ⊥ := by
      rw [hL'eq]
      exact fun h => hc.ne_bot ((Subgroup.map_eq_bot_iff_of_injective (barSub ⊥ V hV L)
        (MulAut.conj φ⁻¹).injective).mp h)
    have hL'M : barSub ⊥ V hV (conjSubgroup L g₀) ≤ Mbar D.M ⊥ V hV := by
      apply barSub_mono
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have hx' : g₀ * x * g₀⁻¹ ∈ D.M := hc.setting.hyp151.le hx
      have hxx : x = g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ := by group
      rw [hxx]
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hg0M) hx') hg0M
    have hgN : g₀ ∉ nBar D.M ⊥ V hV L := by
      rw [s15_Infra_mem_nBar_iff hc.setting.hyp151.hyp125 hV hg0M]
      exact hL'ne
    have hcommW : commSub (wTil ⊥ V hV L) (barSub ⊥ V hV (conjSubgroup L g₀)) = ⊥ :=
      (hc.setting.hyp151.commute g₀ hg0M hgN).2
    have hfix : wTil ⊥ V hV L ≤ fixV (barSub ⊥ V hV (conjSubgroup L g₀)) :=
      commSub_eq_bot_iff.mp hcommW
    have hM₀ : D.M ≤ stabTil ⊥ V :=
      le_stabTil hc.setting.hyp151.hyp125.pairFacts.le_normalizer
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hM₁ : D.M ≤ stabTil (v1Sub D.M ⊥ V hV L) V :=
      le_stabTil hc.setting.hyp151.hyp125.pairFacts.le_normalizer
        (s15_Infra_le_normalizer_v1Sub hc.setting.hyp151.hyp125 hV)
    have hmap := s15_T7_kappa_map_commSub (M := D.M) (V₀ := ⊥)
      (V₁ := v1Sub D.M ⊥ V hV L) (V := V) (L := L) hV
      (s15_Infra_le_v1Sub D.M ⊥ V hV L) hM₀ hM₁ hc.setting.hyp151.le
    have hκmap : (wTil ⊥ V hV L).map κ = ⊤ := by
      change (commSub ⊤ (barSub ⊥ V hV L)).map
        (s15T7Kappa ⊥ (v1Sub D.M ⊥ V hV L) V hV (s15_Infra_le_v1Sub D.M ⊥ V hV L)) = ⊤
      rw [hmap]
      exact hcomm
    have hρfix : ∀ m : ↥(Mbar D.M ⊥ V hV), (m : MulAut (Vtil ⊥ V hV)) ∈
        barSub ⊥ V hV (conjSubgroup L g₀) → ρ m = 1 := by
      intro m hm
      apply Subtype.ext
      apply MulEquiv.ext
      intro y
      have hy : y ∈ (wTil ⊥ V hV L).map κ := by rw [hκmap]; exact Subgroup.mem_top y
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      have hfixw : (m : MulAut (Vtil ⊥ V hV)) w = w :=
        mem_fixV.mp (hfix hw) (m : MulAut (Vtil ⊥ V hV)) hm
      show ((ρ m : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) : MulAut _) y = y
      calc ((ρ m : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) : MulAut _) y
          = ((ρ m : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) : MulAut _) (κ w) := by
            rw [hwy]
        _ = κ ((m : MulAut (Vtil ⊥ V hV)) w) := (hρκ m w).symm
        _ = κ w := by rw [hfixw]
        _ = y := hwy
    have hL'bot : barSub ⊥ V hV (conjSubgroup L g₀) = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have hmM : m ∈ Mbar D.M ⊥ V hV := hL'M hm
      have h1 : ρ ⟨m, hmM⟩ = 1 := hρfix ⟨m, hmM⟩ hm
      have h2 : (⟨m, hmM⟩ : ↥(Mbar D.M ⊥ V hV)) = 1 :=
        ρ.injective (by rw [h1, map_one])
      exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp h2)
    exact hL'ne_bot hL'bot
  have hset : {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, X = (barSub ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} =
      {barSub ⊥ V hV L} := by
    ext X
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact Set.mem_singleton_iff.mpr (hkey φ hφ)
    · intro hX
      rw [Set.mem_singleton_iff] at hX
      subst hX
      exact ⟨1, (Mbar D.M ⊥ V hV).one_mem, (Subgroup.map_id (barSub ⊥ V hV L)).symm⟩
  unfold s15
  rw [hset]
  exact Set.ncard_singleton _

theorem s1611e3_commStar_of_case1 {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (h1 : Case168_1 D ⊥ V hV L) :
    commSub (⊤ : Subgroup (vStar D.M ⊥ V hV L)) (lStar D.M ⊥ V hV L) = ⊤ := by
  obtain ⟨-, -, hsum, -⟩ := h1
  obtain ⟨I₁, I₂, -, -, -, -, hsup, hN₁, hN₂, -⟩ := hsum
  have hc₁ : commSub I₁ (lStar D.M ⊥ V hV L) = I₁ :=
    (s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₁).1
  have hc₂ : commSub I₂ (lStar D.M ⊥ V hV L) = I₂ :=
    (s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₂).1
  have hsup' : I₁ ⊔ I₂ = ⊤ := by
    have h := hsup
    simpa using h
  have hsub : I₁ ⊔ I₂ ≤ commSub ⊤ (lStar D.M ⊥ V hV L) :=
    sup_le (by rw [← hc₁]; exact commSub_mono le_top le_rfl)
      (by rw [← hc₂]; exact commSub_mono le_top le_rfl)
  exact le_antisymm le_top (hsup' ▸ hsub)

theorem s1611e3_commStar_of_case2Star {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (h2 : Case168_2Star D ⊥ V hV L) :
    commSub (⊤ : Subgroup (vStar D.M ⊥ V hV L)) (lStar D.M ⊥ V hV L) = ⊤ := by
  obtain ⟨-, ⟨L₀, hdir, hfam⟩, -⟩ := h2
  rcases hfam with ⟨n, hn5, -, -, -, hsum⟩ | ⟨m, hm3, -, -, -, hsum⟩ |
    ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩
  · exact s1611e3_commSub_top_of_sumOfNat_two hsum
      (fun I hI => s16c167_mem_irrSet_alt (n := n) hn5 hI)
  · exact s1611e3_commSub_top_of_sumOfNat_two hsum
      (fun I hI => s16c167_mem_irrSet_ln (m := m) (by omega) hI)
  · exact s1611e3_commSub_top_of_sumOfNat_two hsum
      (fun I hI => s16c167_mem_irrSet_sp (n := 6) (by norm_num) hI)
  · exact s1611e3_commSub_top_of_sumOfNat_two hsum
      (fun I hI => s16c167_mem_irrSet_omegaMinus (n := 6) (Or.inl rfl) hI)
  · exact s1611e3_commSub_top_of_sumOfNat_two hsum
      (fun I hI => s16c167_mem_irrSet_omegaMinus (n := 8) (Or.inr rfl) hI)

theorem s1611e3_commStar_of_case5Star {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (h5 : Case168_5Star D ⊥ V hV L) :
    commSub (⊤ : Subgroup (vStar D.M ⊥ V hV L)) (lStar D.M ⊥ V hV L) = ⊤ := by
  obtain ⟨-, -, hnat, -⟩ := h5
  obtain ⟨t₁, ht₁, -, -, -, -, -, hfix, -, -⟩ := s16c11_v1_natOmegaPlus_two_fpf_in hnat
  let f : vStar D.M ⊥ V hV L →* vStar D.M ⊥ V hV L := t₁.toMonoidHom * invMonoidHom
  have hf1 : ∀ x, f x = 1 → x = 1 := by
    intro x hx
    apply hfix
    have hx' : t₁ x * x⁻¹ = 1 := by simpa [f] using hx
    exact mul_inv_eq_one.mp hx'
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : f (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hf1 _ h1)
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  refine le_antisymm le_top ?_
  intro y _
  obtain ⟨x, hx⟩ := hsurj y
  refine Subgroup.subset_closure ⟨t₁, ht₁, x, Subgroup.mem_top x, ?_⟩
  rw [← hx]
  simp [f]

theorem s1611e3_s15_eq_one_of_starred {D : Data G} (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hcase : Case168_1 D ⊥ V hV L ∨ Case168_2Star D ⊥ V hV L ∨ Case168_5Star D ⊥ V hV L) :
    s15 D.M ⊥ V hV L = 1 := by
  refine s1611e3_s15_eq_one_of_commStar h.h1217 hc ?_
  rcases hcase with h1 | h2 | h5
  · exact s1611e3_commStar_of_case1 hc h1
  · exact s1611e3_commStar_of_case2Star hc h2
  · exact s1611e3_commStar_of_case5Star hc h5

theorem s1611e3_exists_noncyclic_three_of_sym {A : Type} [Group A] {K L₀ M : Subgroup A}
    (hK : IsSym ↥K 3) (hdir : IsInternalDirect K L₀ M) {n : ℕ} (hn : 3 ≤ n)
    (hL₀ : IsSym ↥L₀ n) : ∃ P : Subgroup A, P ≤ M ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P := by
  obtain ⟨eK⟩ := hK
  obtain ⟨eL⟩ := hL₀
  let c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hc3pow : c3 ^ 3 = 1 := by decide
  have hc3ne : c3 ≠ 1 := by decide
  let z : ↥K := eK.symm c3
  have hez : eK z = c3 := MulEquiv.apply_symm_apply eK c3
  have hzpow : z ^ 3 = 1 := by
    apply eK.injective
    rw [map_pow, hez, hc3pow, map_one]
  have hzne : z ≠ 1 := by
    intro h
    apply hc3ne
    rw [← hez, h, map_one]
  let emb : Fin 3 ↪ Fin n := Fin.castLEEmb hn
  let φ : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin n) := Equiv.Perm.viaEmbeddingHom emb
  have hφinj : Function.Injective φ := Equiv.Perm.viaEmbeddingHom_injective emb
  let d3 : Equiv.Perm (Fin n) := φ c3
  have hd3pow : d3 ^ 3 = 1 := by
    rw [show d3 = φ c3 from rfl, ← map_pow, hc3pow, map_one]
  have hd3ne : d3 ≠ 1 := by
    intro h
    have h1 : φ c3 = φ 1 := by rw [map_one]; exact h
    exact hc3ne (hφinj h1)
  let c : ↥L₀ := eL.symm d3
  have hec : eL c = d3 := MulEquiv.apply_symm_apply eL d3
  have hcpow : c ^ 3 = 1 := by
    apply eL.injective
    rw [map_pow, hec, hd3pow, map_one]
  have hcne : c ≠ 1 := by
    intro h
    apply hd3ne
    rw [← hec, h, map_one]
  let zA : A := (z : A)
  let cA : A := (c : A)
  have hzApow : zA ^ 3 = 1 := by
    have h := congrArg (fun x : ↥K => (x : A)) hzpow
    simpa [zA] using h
  have hzAne : zA ≠ 1 := by
    intro h
    exact hzne (Subtype.ext (by simpa [zA] using h))
  have hcApow : cA ^ 3 = 1 := by
    have h := congrArg (fun x : ↥L₀ => (x : A)) hcpow
    simpa [cA] using h
  have hcAne : cA ≠ 1 := by
    intro h
    exact hcne (Subtype.ext (by simpa [cA] using h))
  have hzAK : zA ∈ K := z.2
  have hcAL : cA ∈ L₀ := c.2
  have hcomm : Commute zA cA := by
    have hcent : zA ∈ Subgroup.centralizer (L₀ : Set A) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := L₀)).1 hdir.1 hzAK
    exact (Subgroup.mem_centralizer_iff.1 hcent cA hcAL).symm
  let P : Subgroup A := Subgroup.zpowers zA ⊔ Subgroup.zpowers cA
  have hKM : K ≤ M := hdir.2.2 ▸ le_sup_left
  have hLM : L₀ ≤ M := hdir.2.2 ▸ le_sup_right
  have hPM : P ≤ M :=
    sup_le ((Subgroup.zpowers_le.mpr hzAK).trans hKM) ((Subgroup.zpowers_le.mpr hcAL).trans hLM)
  have hzcard : Nat.card ↥(Subgroup.zpowers zA) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hzApow hzAne]
  have hccard : Nat.card ↥(Subgroup.zpowers cA) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hcApow hcAne]
  have hinf : Subgroup.zpowers zA ⊓ Subgroup.zpowers cA = ⊥ := by
    refine le_bot_iff.mp ?_
    calc Subgroup.zpowers zA ⊓ Subgroup.zpowers cA
        ≤ K ⊓ L₀ := inf_le_inf (Subgroup.zpowers_le.mpr hzAK) (Subgroup.zpowers_le.mpr hcAL)
      _ = ⊥ := hdir.2.1
  have hexp : ∀ g : ↥P, g ^ 3 = 1 := by
    intro g
    have hx : (g : A) ∈ Subgroup.zpowers zA ⊔ Subgroup.zpowers cA := g.2
    obtain ⟨i, j, hgij⟩ := s1611e3_exists_zpow_mul_zpow_of_mem_sup hcomm hx
    have hzi : (zA ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast (zA ^ i) 3, ← zpow_mul]
      exact (zpow_mul' zA i ((3 : ℕ) : ℤ)).trans (by rw [zpow_natCast, hzApow, one_zpow])
    have hcj : (cA ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast (cA ^ j) 3, ← zpow_mul]
      exact (zpow_mul' cA j ((3 : ℕ) : ℤ)).trans (by rw [zpow_natCast, hcApow, one_zpow])
    have hmain : (g : A) ^ 3 = 1 := by
      rw [hgij]
      calc (zA ^ i * cA ^ j) ^ 3 = (zA ^ i) ^ 3 * (cA ^ j) ^ 3 :=
            (hcomm.zpow_zpow i j).mul_pow 3
        _ = 1 := by rw [hzi, hcj, mul_one]
    exact Subtype.ext (by simpa using hmain)
  refine ⟨P, hPM, ?_, ?_⟩
  · exact fun g => ⟨1, by simpa using hexp g⟩
  · intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥P)
    have hg3 : g ^ 3 = 1 := hexp g
    have hdvd : Nat.card ↥P ∣ 3 := by rw [← hg]; exact orderOf_dvd_of_pow_eq_one hg3
    have h3dvd : 3 ∣ Nat.card ↥P := by
      have hle : Subgroup.zpowers zA ≤ P :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers zA))
      have h := Subgroup.card_dvd_of_le hle
      rwa [hzcard] at h
    have hcardP : Nat.card ↥P = 3 := (Nat.dvd_antisymm h3dvd hdvd).symm
    haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hcardP]; norm_num)
    haveI : Finite ↥(Subgroup.zpowers zA) :=
      Nat.finite_of_card_ne_zero (by rw [hzcard]; norm_num)
    have hzP : Subgroup.zpowers zA = P :=
      Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers zA)))
        (by rw [hcardP, hzcard])
    have hcP : Subgroup.zpowers cA ≤ Subgroup.zpowers zA := by
      rw [hzP]
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers cA))
    have hcz : Subgroup.zpowers cA = Subgroup.zpowers zA :=
      Subgroup.eq_of_le_of_card_ge hcP (by rw [hzcard, hccard])
    have hbot : Subgroup.zpowers zA = ⊥ := by
      rw [← hinf, hcz, inf_idem]
    exact (Subgroup.zpowers_ne_bot.mpr hzAne) hbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
