module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

private theorem exists_equivariant_hom_of_split {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I) {T : Subgroup (MulAut W)}
    (hTL : T ≤ L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {v0 : W} (hv0J : v0 ∈ J) (hv0T : v0 ∈ fixV T) (hv0ne : v0 ≠ 1)
    {I D : Subgroup W} (hI : I ∈ irrSet L) {d : W} {φD : ↥J →* W}
    (hφDv0 : φD ⟨v0, hv0J⟩ = d) (hφDrange : ∀ x : ↥J, φD x ∈ D)
    (hφDequiv : ∀ l ∈ L, ∀ (x : ↥J) (h : l (x : W) ∈ J),
      φD ⟨l (x : W), h⟩ = l (φD x))
    {i : W} (hiI : i ∈ I) (hiT : i ∈ fixV T) :
    ∃ φ : ↥J →* W, φ ⟨v0, hv0J⟩ = i * d ∧ (∀ x : ↥J, φ x ∈ I ⊔ D) ∧
      ∀ l ∈ L, ∀ (x : ↥J) (h : l (x : W) ∈ J),
        φ ⟨l (x : W), h⟩ = l (φ x) := by
  classical
  obtain ⟨ψ, hψ⟩ := hhom I hI
  have hψv0I : ((ψ ⟨v0, hv0J⟩ : ↥I) : W) ∈ I := (ψ ⟨v0, hv0J⟩).2
  have hψv0T : ((ψ ⟨v0, hv0J⟩ : ↥I) : W) ∈ fixV T := by
    intro t ht
    have hv0t : t v0 = v0 := mem_fixV.mp hv0T t ht
    have hmem : t v0 ∈ J := by rw [hv0t]; exact hv0J
    have heq := hψ t (hTL ht) ⟨v0, hv0J⟩ hmem
    have hsub : (⟨t v0, hmem⟩ : ↥J) = ⟨v0, hv0J⟩ := Subtype.ext hv0t
    rw [hsub] at heq
    exact heq.symm
  have hψv0ne : ((ψ ⟨v0, hv0J⟩ : ↥I) : W) ≠ 1 := by
    intro h
    have h1 : ψ ⟨v0, hv0J⟩ = 1 := Subtype.ext h
    have h2 : (⟨v0, hv0J⟩ : ↥J) = 1 := ψ.injective (by simpa using h1)
    exact hv0ne (by simpa using congrArg Subtype.val h2)
  by_cases hi1 : i = 1
  · refine ⟨φD, ?_, ?_, hφDequiv⟩
    · rw [hi1, hφDv0, one_mul]
    · intro x; exact Subgroup.mem_sup_right (hφDrange x)
  · obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : ↥(I ⊓ fixV T))).mp (hT I hI)
    have hi_eq : (⟨i, Subgroup.mem_inf.mpr ⟨hiI, hiT⟩⟩ : ↥(I ⊓ fixV T)) = w :=
      hw _ (fun h => hi1 (congrArg Subtype.val h))
    have hψ_eq : (⟨((ψ ⟨v0, hv0J⟩ : ↥I) : W),
        Subgroup.mem_inf.mpr ⟨hψv0I, hψv0T⟩⟩ : ↥(I ⊓ fixV T)) = w :=
      hw _ (fun h => hψv0ne (congrArg Subtype.val h))
    have hieq : i = ((ψ ⟨v0, hv0J⟩ : ↥I) : W) :=
      congrArg Subtype.val (hi_eq.trans hψ_eq.symm)
    let ψW : ↥J →* W := I.subtype.comp ψ.toMonoidHom
    let φ : ↥J →* W := ψW * φD
    refine ⟨φ, ?_, ?_, ?_⟩
    · have hv : φ ⟨v0, hv0J⟩ = ψW ⟨v0, hv0J⟩ * φD ⟨v0, hv0J⟩ := by
        simp [φ, MonoidHom.mul_apply]
      have hψWv0 : ψW ⟨v0, hv0J⟩ = i := hieq.symm
      rw [hv, hφDv0, hψWv0]
    · intro x; exact Subgroup.mul_mem_sup (ψ x).2 (hφDrange x)
    · intro l hl x h
      have hψeq : ψW ⟨l (x : W), h⟩ = l (ψW x) := hψ l hl x h
      have hφDeq := hφDequiv l hl x h
      calc φ ⟨l (x : W), h⟩ = ψW ⟨l (x : W), h⟩ * φD ⟨l (x : W), h⟩ := by
            simp [φ, MonoidHom.mul_apply]
        _ = l (ψW x) * l (φD x) := by rw [hψeq, hφDeq]
        _ = l (ψW x * φD x) := (map_mul l _ _).symm
        _ = l (φ x) := by simp [φ, MonoidHom.mul_apply]

private theorem exists_equivariant_hom [Finite W] {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {J : Subgroup W}
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I) {T : Subgroup (MulAut W)}
    (hTL : T ≤ L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {v0 : W} (hv0J : v0 ∈ J) (hv0T : v0 ∈ fixV T) (hv0ne : v0 ≠ 1)
    {S : Subgroup W} (hS : StableUnder L S) {u : W} (huS : u ∈ S) (huT : u ∈ fixV T) :
    ∃ φ : ↥J →* W, φ ⟨v0, hv0J⟩ = u ∧ (∀ x : ↥J, φ x ∈ S) ∧
      ∀ l ∈ L, ∀ (x : ↥J) (h : l (x : W) ∈ J),
        φ ⟨l (x : W), h⟩ = l (φ x) := by
  classical
  have key : ∀ n, ∀ S : Subgroup W, Nat.card S = n → StableUnder L S →
      ∀ u : W, u ∈ S → u ∈ fixV T →
      ∃ φ : ↥J →* W, φ ⟨v0, hv0J⟩ = u ∧ (∀ x : ↥J, φ x ∈ S) ∧
        ∀ l ∈ L, ∀ (x : ↥J) (h : l (x : W) ∈ J),
          φ ⟨l (x : W), h⟩ = l (φ x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hScard hSstab u huS huT
      by_cases hSbot : S = ⊥
      · subst S
        have hu1 : u = 1 := by simpa using huS
        subst u
        exact ⟨1, by simp, by intro x; simp, by intro l hl x h; simp⟩
      · obtain ⟨I, D, hI, -, -, hDstab, hID, hIDsup, hDltn⟩ :=
          exists_invariant_compl_lt hfix hspan hSstab hSbot hScard
        have huSup : u ∈ I ⊔ D := by rw [hIDsup]; exact huS
        obtain ⟨i, hiI, d, hdD, hid⟩ := Subgroup.mem_sup.mp huSup
        have hfix_pair : ∀ t ∈ T, t i = i ∧ t d = d := by
          intro t ht
          have htiI : t i ∈ I :=
            CFSG.LocalAnalysis.WeakClosure81.stableUnder_of_mem_irrSet hI t (hTL ht) i hiI
          have htdD : t d ∈ D := hDstab t (hTL ht) d hdD
          have htu : t u = u := mem_fixV.mp huT t ht
          have h_eq : (t i) * (t d) = i * d := by
            calc (t i) * (t d) = t (i * d) := (map_mul t i d).symm
              _ = t u := by rw [hid]
              _ = u := htu
              _ = i * d := hid.symm
          exact CFSG.Quasithin.H.Pair.decomp_unique hID htiI htdD hiI hdD h_eq
        have hiT : i ∈ fixV T := fun t ht => (hfix_pair t ht).1
        have hdT : d ∈ fixV T := fun t ht => (hfix_pair t ht).2
        obtain ⟨φD, hφDv0, hφDrange, hφDequiv⟩ :=
          ih (Nat.card D) hDltn D rfl hDstab d hdD hdT
        obtain ⟨φ, hφv0, hφrange, hφequiv⟩ :=
          exists_equivariant_hom_of_split hhom hTL hT hv0J hv0T hv0ne hI
            hφDv0 hφDrange hφDequiv hiI hiT
        refine ⟨φ, ?_, ?_, hφequiv⟩
        · rw [hφv0, hid]
        · intro x; rw [← hIDsup]; exact hφrange x
  exact key (Nat.card S) S rfl hS u huS huT

private theorem rk_iSup_zpowers_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤)
    {J : Subgroup W} (hJ : J ∈ irrSet L)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I) {T : Subgroup (MulAut W)}
    (hTL : T ≤ L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {u : W} (huT : u ∈ fixV T) :
    rk ↥(⨆ g ∈ L, (Subgroup.zpowers u).map (g : MulAut W).toMonoidHom) ≤ rk ↥J := by
  classical
  obtain ⟨w, hwne, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(J ⊓ fixV T))).mp (hT J hJ)
  have hv0J : (w : W) ∈ J := (Subgroup.mem_inf.mp w.2).1
  have hv0T : (w : W) ∈ fixV T := (Subgroup.mem_inf.mp w.2).2
  have hv0ne : (w : W) ≠ 1 := fun h => hwne (Subtype.ext h)
  obtain ⟨φ, hφv0, -, hφequiv⟩ := exists_equivariant_hom hfix hspan hhom hTL hT hv0J hv0T
    hv0ne (S := ⊤) (by intro l hl x hx; exact Subgroup.mem_top _) (u := u)
    (Subgroup.mem_top _) huT
  have hrange_stab : StableUnder L φ.range := by
    intro l hl y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    have hmem : l (x : W) ∈ J :=
      CFSG.LocalAnalysis.WeakClosure81.stableUnder_of_mem_irrSet hJ l hl x x.2
    exact MonoidHom.mem_range.mpr ⟨⟨l (x : W), hmem⟩, hφequiv l hl x hmem⟩
  have hu_range : u ∈ φ.range := MonoidHom.mem_range.mpr ⟨⟨w, hv0J⟩, hφv0⟩
  have hle : (⨆ g ∈ L, (Subgroup.zpowers u).map (g : MulAut W).toMonoidHom) ≤ φ.range := by
    refine iSup₂_le fun g hg => ?_
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr (hrange_stab g hg u hu_range)
  have hcard_le : Nat.card ↥(φ.range) ≤ Nat.card ↥J :=
    Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective φ)
  have hrange_le : rk ↥(φ.range) ≤ rk ↥J := by
    have hpow : 2 ^ rk ↥(φ.range) ≤ 2 ^ rk ↥J := by
      rw [← card_eq_two_pow hW (φ.range), ← card_eq_two_pow hW J]
      exact hcard_le
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  exact (rk_mono hle).trans hrange_le

private theorem exists_index_two_decomp [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup W} (hA1 : A ≠ ⊥) :
    ∃ A' : Subgroup W, A' ≤ A ∧ rk ↥A' = rk ↥A - 1 ∧
      ∃ u ∈ A, u ∉ A' ∧ A' ⊔ Subgroup.zpowers u = A := by
  classical
  have hA2 : Nat.card ↥A = 2 ^ rk ↥A := card_eq_two_pow hW A
  have hrk_pos : 0 < rk ↥A := by
    by_contra h
    exact hA1 ((rk_eq_zero_iff hW).mp (Nat.eq_zero_of_not_pos h))
  have hdvd : 2 ^ (rk ↥A - 1) ∣ Nat.card ↥A := by
    rw [hA2]
    exact pow_dvd_pow 2 (Nat.sub_le _ _)
  obtain ⟨B, hBcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := ↥A) 2 (n := rk ↥A - 1) hdvd
  let A' : Subgroup W := B.map A.subtype
  have hA'leA : A' ≤ A := Subgroup.map_subtype_le B
  have hA'cardB : Nat.card ↥A' = Nat.card ↥B :=
    Subgroup.card_map_of_injective A.subtype_injective
  have hA'card : Nat.card ↥A' = 2 ^ (rk ↥A - 1) := by rw [hA'cardB, hBcard]
  have hrk_eq : rk ↥A = (rk ↥A - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_of_lt hrk_pos)).symm
  have hcardA : Nat.card ↥A = 2 * Nat.card ↥A' := by
    rw [hA2, hA'card, Nat.mul_comm 2 (2 ^ (rk ↥A - 1)), ← pow_succ]
    exact congrArg (fun n => 2 ^ n) hrk_eq
  have hA'rel : A'.relIndex A = 2 := by
    have h := Subgroup.relIndex_mul_card (H := A') (K := A)
    rw [inf_of_le_left hA'leA] at h
    rw [hcardA] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hA'rk : rk ↥A' = rk ↥A - 1 := by
    change padicValNat 2 (Nat.card ↥A') = padicValNat 2 (Nat.card ↥A) - 1
    rw [hA'cardB, hBcard, hA2, padicValNat.prime_pow, padicValNat.prime_pow]
  have hidx_sub : (A'.subgroupOf A).index = 2 := by
    simpa [Subgroup.relIndex] using hA'rel
  obtain ⟨uA, huA'not, hcover⟩ :=
    (Subgroup.index_eq_two_iff_exists_notMem_and (H := A'.subgroupOf A)).mp hidx_sub
  refine ⟨A', hA'leA, hA'rk, ⟨uA.1, uA.2, ?_, ?_⟩⟩
  · intro hu
    exact huA'not (Subgroup.mem_subgroupOf.mpr hu)
  · refine le_antisymm (sup_le hA'leA (Subgroup.zpowers_le.mpr uA.2)) ?_
    intro b hbA
    let bA : ↥A := ⟨b, hbA⟩
    rcases hcover bA with hbu | hbA'
    · have hbu' : b * uA.1 ∈ A' := Subgroup.mem_subgroupOf.mp hbu
      have hb_eq : b = (b * uA.1) * uA.1⁻¹ := (mul_inv_cancel_right b uA.1).symm
      rw [hb_eq]
      exact Subgroup.mul_mem_sup hbu' (Subgroup.inv_mem _ (Subgroup.mem_zpowers uA.1))
    · exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hbA')

private theorem rk_sup_le [Finite W] {X Y : Subgroup W} :
    rk ↥(X ⊔ Y) ≤ rk ↥X + rk ↥Y := by
  have h := rk_sup_add_rk_inf X Y
  omega

private theorem rk_iSup_map_le_aux [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤)
    {J : Subgroup W} (hJ : J ∈ irrSet L)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I) {T : Subgroup (MulAut W)}
    (hTL : T ≤ L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {A : Subgroup W} (hA : A ≤ fixV T) :
    rk ↥(⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom) ≤ rk ↥J * rk ↥A := by
  classical
  let spanMap : Subgroup W → Subgroup W := fun B =>
    ⨆ g ∈ L, B.map (g : MulAut W).toMonoidHom
  change rk ↥(spanMap A) ≤ rk ↥J * rk ↥A
  have key : ∀ n, ∀ A : Subgroup W, Nat.card A = n → A ≤ fixV T →
      rk ↥(spanMap A) ≤ rk ↥J * rk ↥A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hAcard hAle
      by_cases hAbot : A = ⊥
      · subst A
        have hbot : spanMap ⊥ = ⊥ := by simp [spanMap]
        rw [hbot]
        simp [rk_bot]
      · obtain ⟨A', hA'leA, hA'rk, u, huA, huA', hsup⟩ := exists_index_two_decomp hW hAbot
        have hA'le_fixV : A' ≤ fixV T := hA'leA.trans hAle
        have hA'neA : A' ≠ A := by
          intro h
          exact huA' (h.symm ▸ huA)
        have hA'card_lt : Nat.card ↥A' < Nat.card ↥A := by
          refine lt_of_le_of_ne (Subgroup.card_le_of_le hA'leA) ?_
          intro hcard
          exact hA'neA (Subgroup.eq_of_le_of_card_ge hA'leA (by rw [hcard]))
        have hA'ltn : Nat.card ↥A' < n := by rw [← hAcard]; exact hA'card_lt
        have hIH := ih (Nat.card ↥A') hA'ltn A' rfl hA'le_fixV
        have hzpow : rk ↥(spanMap (Subgroup.zpowers u)) ≤ rk ↥J :=
          rk_iSup_zpowers_le hW hfix hspan hJ hhom hTL hT (hAle huA)
        have hrk_pos : 0 < rk ↥A := by
          by_contra h
          exact hAbot ((rk_eq_zero_iff hW).mp (Nat.eq_zero_of_not_pos h))
        have hAdecomp : rk ↥A = (rk ↥A - 1) + 1 :=
          (Nat.sub_add_cancel (Nat.succ_le_of_lt hrk_pos)).symm
        have hspan_eq : spanMap A = spanMap A' ⊔ spanMap (Subgroup.zpowers u) := by
          simp only [spanMap, ← hsup, Subgroup.map_sup, iSup_sup_eq]
        rw [hspan_eq]
        calc rk ↥(spanMap A' ⊔ spanMap (Subgroup.zpowers u))
            ≤ rk ↥(spanMap A') + rk ↥(spanMap (Subgroup.zpowers u)) := rk_sup_le
          _ ≤ rk ↥J * rk ↥A' + rk ↥J := add_le_add hIH hzpow
          _ = rk ↥J * rk ↥A := by
              rw [hA'rk]
              conv_rhs => rw [hAdecomp]
              ring
  exact key (Nat.card A) A rfl hA

theorem rk_iSup_map_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {J : Subgroup W} (hJ : J ∈ irrSet L)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I) {T : Subgroup (MulAut W)}
    (hTL : T ≤ L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2) {A : Subgroup W}
    (hA : A ≤ fixV T) :
    rk ↥(⨆ g ∈ L, A.map (g : MulAut W).toMonoidHom) ≤ rk ↥J * rk ↥A :=
  rk_iSup_map_le_aux hW hfix hspan hJ hhom hTL hT hA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
