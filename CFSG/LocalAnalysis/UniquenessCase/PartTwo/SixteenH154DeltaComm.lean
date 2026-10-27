module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154DeltaSupp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154DeltaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Perm
public import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

theorem s16h_dc_core {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} {p r : ℕ} {Wsub : Subgroup W} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hpr : ¬ (p = 3 ∧ r = 2)) (hLA : L ≤ A) (hLst : L ≤ stabSub Wsub)
    (hLn : ∀ g ∈ A ⊓ stabSub Wsub, L.map (MulAut.conj g).toMonoidHom = L)
    (hfaith : ∀ l ∈ L, (∀ u ∈ Wsub, l u = u) → l = 1) (hE : IsElemAbelianOfRank p r ↥L)
    (hLt : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) {Δ : Fin (r + 1) → Subgroup W} (hsup : (⨆ i, Δ i) = Wsub)
    {σ : ↥(A ⊓ stabSub Wsub) →* Equiv.Perm (Fin (r + 1))} (hσsurj : Function.Surjective σ)
    (hσact : ∀ (g : ↥(A ⊓ stabSub Wsub)) (i : Fin (r + 1)),
      (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i))
    (ht : t ∈ A ⊓ stabSub Wsub) (hswap : (σ ⟨t, ht⟩).IsSwap)
    (hfix : ∀ i, σ ⟨t, ht⟩ i = i → ∀ x ∈ Δ i, t x = x) : L ≤ ⁅A, A⁆ := by
  have hLd : ∀ l ∈ L, l ∈ A ⊓ stabSub Wsub := fun l hl => ⟨hLA hl, hLst hl⟩
  have hHnorm : (L.subgroupOf (A ⊓ stabSub Wsub)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hmem : (MulAut.conj (g : MulAut W)).toMonoidHom (n : MulAut W) ∈
        L.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hn
    rw [hLn (g : MulAut W) g.2] at hmem
    simpa [MulAut.conj_apply] using hmem
  let N : Subgroup (Equiv.Perm (Fin (r + 1))) := (L.subgroupOf (A ⊓ stabSub Wsub)).map σ
  have hNnorm : N.Normal := hHnorm.map σ hσsurj
  have hNpow : ∀ a ∈ N, a ^ p = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_pow]
    have h := s16h_dc_pow_eq_one_of_elem hE
      (⟨(a' : MulAut W), Subgroup.mem_subgroupOf.mp ha'⟩ : ↥L)
    have h1 : a' ^ p = 1 := Subtype.ext (by simpa using congrArg Subtype.val h)
    rw [h1, map_one]
  have hNp : IsPGroup p ↥N := fun a => ⟨1, Subtype.ext (by simpa using hNpow a a.2)⟩
  have hNbot : N = ⊥ := by
    by_cases h4 : 4 ≤ r + 1
    · exact s16n9b_case4_perm_normal hp hp2 (by rw [Fintype.card_fin]; exact h4) hNnorm hNp
    · refine s16n9b_case4_perm_small hp ?_ hNp
      have hr2 : r = 2 := by omega
      have hp3 : p ≠ 3 := fun h => hpr ⟨h, hr2⟩
      have hp5 : 5 ≤ p := by
        by_contra hlt
        have h4 : p = 4 := by have := hp.two_le; omega
        exact absurd (h4 ▸ hp) (by norm_num)
      rw [Fintype.card_fin]
      omega
  have hσL : ∀ d : ↥(A ⊓ stabSub Wsub), (d : MulAut W) ∈ L → σ d = 1 := by
    intro d hd
    have hmem : σ d ∈ N := Subgroup.mem_map_of_mem σ (Subgroup.mem_subgroupOf.mpr hd)
    rw [hNbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hmapL : ∀ l ∈ L, ∀ i, (Δ i).map l.toMonoidHom = Δ i := by
    intro l hl i
    have h := hσact ⟨l, hLd l hl⟩ i
    rw [hσL ⟨l, hLd l hl⟩ hl, Equiv.Perm.one_apply] at h
    simpa using h
  obtain ⟨l, hlL, hly⟩ := s16h_dc_exists_commutator_ne_one_zpowers hLt
  let y : MulAut W := ⁅l, t⁆
  have hy_ne : y ≠ 1 := hly
  have hyL : y ∈ L := by
    have hconj : (MulAut.conj t) l⁻¹ ∈ L := by
      rw [← hLn t ht]
      exact Subgroup.mem_map_of_mem _ (L.inv_mem hlL)
    have hy_eq : y = l * (MulAut.conj t) l⁻¹ := by
      simp [y, commutatorElement_def, MulAut.conj_apply, mul_assoc]
    rw [hy_eq]
    exact L.mul_mem hlL hconj
  obtain ⟨a, b, hab, hσt⟩ := hswap
  have hy_supp_sub : s16h_dc_supp Δ y ⊆ ({a, b} : Set (Fin (r + 1))) := by
    intro k hk
    by_contra hkab
    have hka : k ≠ a := by rintro rfl; exact hkab (by simp)
    have hkb : k ≠ b := by rintro rfl; exact hkab (by simp)
    have hkfix : ∀ x ∈ Δ k, t x = x :=
      hfix k (by rw [hσt, Equiv.swap_apply_of_ne_of_ne hka hkb])
    obtain ⟨x, hx, hne⟩ := hk
    apply hne
    have htinv : t⁻¹ x = x := by
      apply t.injective
      simpa [hkfix x hx] using (MulEquiv.apply_symm_apply t x)
    have hlinv : l⁻¹ x ∈ Δ k := by
      have hmap := hmapL l⁻¹ (L.inv_mem hlL) k
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hx
    have htx : t (l⁻¹ x) = l⁻¹ x := hkfix _ hlinv
    have hy_eq : y = l * t * l⁻¹ * t⁻¹ := rfl
    rw [hy_eq]
    calc (l * t * l⁻¹ * t⁻¹) x = l (t (l⁻¹ (t⁻¹ x))) := rfl
      _ = l (t (l⁻¹ x)) := by rw [htinv]
      _ = l (l⁻¹ x) := by rw [htx]
      _ = x := by simp
  have hy_supp_ne : s16h_dc_supp Δ y ≠ ∅ := fun h =>
    hy_ne (s16h_dc_eq_one_of_supp_empty hsup hfaith hyL h)
  have hy_not_singleton : ¬ ∃ c, s16h_dc_supp Δ y = {c} := by
    rintro ⟨c, hc⟩
    exact s16h_dc_supp_not_singleton hp hE hLn hσsurj hσact hyL hc
  have hy_supp : s16h_dc_supp Δ y = {a, b} := by
    by_cases ha : a ∈ s16h_dc_supp Δ y <;> by_cases hb : b ∈ s16h_dc_supp Δ y
    · exact Set.Subset.antisymm hy_supp_sub (by
        intro w hw
        rcases hw with rfl | rfl
        · exact ha
        · exact hb)
    · exact absurd ⟨a, Set.eq_singleton_iff_unique_mem.mpr ⟨ha, fun z hz => by
        rcases hy_supp_sub hz with hza | hzb
        · exact hza
        · exact absurd (hzb ▸ hz) hb⟩⟩ hy_not_singleton
    · exact absurd ⟨b, Set.eq_singleton_iff_unique_mem.mpr ⟨hb, fun z hz => by
        rcases hy_supp_sub hz with hza | hzb
        · exact absurd (hza ▸ hz) ha
        · exact hzb⟩⟩ hy_not_singleton
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hy_supp_ne
      rcases hy_supp_sub hx with hxa | hxb
      · exact absurd (hxa ▸ hx) ha
      · exact absurd (hxb ▸ hx) hb
  have hperm : ∀ m : Fin r, ∃ g : ↥(A ⊓ stabSub Wsub),
      σ g = Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m) *
        Equiv.swap a (Fin.castSucc m) := fun m => hσsurj _
  choose g hg using hperm
  let u : Fin r → MulAut W := fun m => (g m : MulAut W) * y * (g m : MulAut W)⁻¹
  have hu_supp : ∀ m : Fin r, s16h_dc_supp Δ (u m) = {Fin.castSucc m, Fin.succ m} := by
    intro m
    have hpc : Fin.castSucc m ≠ Equiv.swap a (Fin.castSucc m) b := by
      intro h
      have h' : a = b := by
        have h2 := congrArg (Equiv.swap a (Fin.castSucc m)) h
        simpa using h2
      exact hab h'
    have hpq : Fin.castSucc m ≠ Fin.succ m := ne_of_lt (Fin.castSucc_lt_succ (i := m))
    have hπa : (Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m) *
        Equiv.swap a (Fin.castSucc m) : Equiv.Perm (Fin (r + 1))) a = Fin.castSucc m := by
      show Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m)
          (Equiv.swap a (Fin.castSucc m) a) = Fin.castSucc m
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hpc hpq]
    have hπb : (Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m) *
        Equiv.swap a (Fin.castSucc m) : Equiv.Perm (Fin (r + 1))) b = Fin.succ m := by
      show Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m)
          (Equiv.swap a (Fin.castSucc m) b) = Fin.succ m
      rw [Equiv.swap_apply_left]
    have h := s16h_dc_supp_conj (A := A) hσact (g m) y
    rw [hy_supp, hg m] at h
    rw [show u m = (g m : MulAut W) * y * (g m : MulAut W)⁻¹ from rfl, h,
      Set.image_insert_eq, Set.image_singleton, hπa, hπb]
  have huL : ∀ m, u m ∈ L := by
    intro m
    have hconj : (MulAut.conj (g m : MulAut W)) y ∈ L := by
      rw [← hLn (g m : MulAut W) (g m).2]
      exact Subgroup.mem_map_of_mem _ hyL
    simpa [u, MulAut.conj_apply] using hconj
  have hu_comm : ∀ m, u m ∈ ⁅A, A⁆ := by
    intro m
    have hgA : (g m : MulAut W) ∈ A := (Subgroup.mem_inf.mp (g m).2).1
    have htA : t ∈ A := (Subgroup.mem_inf.mp ht).1
    have hlA : l ∈ A := hLA hlL
    have h1 : (MulAut.conj (g m : MulAut W)) l ∈ A :=
      A.mul_mem (A.mul_mem hgA hlA) (A.inv_mem hgA)
    have h2 : (MulAut.conj (g m : MulAut W)) t ∈ A :=
      A.mul_mem (A.mul_mem hgA htA) (A.inv_mem hgA)
    have hmem : ⁅(MulAut.conj (g m : MulAut W)) l, (MulAut.conj (g m : MulAut W)) t⁆ ∈
        ⁅A, A⁆ := Subgroup.commutator_mem_commutator h1 h2
    have hu_eq : u m = ⁅(MulAut.conj (g m : MulAut W)) l, (MulAut.conj (g m : MulAut W)) t⁆ := by
      have h1 : u m = (MulAut.conj (g m : MulAut W)).toMonoidHom y := rfl
      rw [h1]
      simpa [y] using map_commutatorElement (MulAut.conj (g m : MulAut W)).toMonoidHom l t
    rw [hu_eq]
    exact hmem
  have hu_mem : ∀ m, Fin.castSucc m ∈ s16h_dc_supp Δ (u m) := fun m => by
    rw [hu_supp m]
    exact Set.mem_insert _ _
  have hu_tri : ∀ m j, m < j → Fin.castSucc m ∉ s16h_dc_supp Δ (u j) := by
    intro m j hmj
    rw [hu_supp j]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · have := congrArg Fin.val h
      simp only [Fin.val_castSucc] at this
      omega
    · have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
  have hcard_u : p ^ r ≤ Nat.card ↥(Subgroup.closure (Set.range u)) :=
    s16h_dc_triangular_card (L := L) (s := r) (i := Fin.castSucc) hp hE huL hu_mem hu_tri
  have hLcard : Nat.card ↥L = p ^ r := s16h_dc_card_of_elem hE
  have hclosure_le_L : Subgroup.closure (Set.range u) ≤ L :=
    (Subgroup.closure_le L).mpr (by rintro _ ⟨m, rfl⟩; exact huL m)
  have hclosure_le_comm : Subgroup.closure (Set.range u) ≤ ⁅A, A⁆ :=
    (Subgroup.closure_le ⁅A, A⁆).mpr (by rintro _ ⟨m, rfl⟩; exact hu_comm m)
  have hcard_le : Nat.card ↥(Subgroup.closure (Set.range u)) ≤ Nat.card ↥L :=
    Subgroup.card_le_of_le hclosure_le_L
  have heq_card : Nat.card ↥(Subgroup.closure (Set.range u)) = Nat.card ↥L :=
    le_antisymm hcard_le (by rw [hLcard]; exact hcard_u)
  have hclosure_eq : Subgroup.closure (Set.range u) = L :=
    Subgroup.eq_of_le_of_card_ge hclosure_le_L (le_of_eq heq_card.symm)
  intro x hx
  exact hclosure_le_comm (hclosure_eq ▸ hx)

theorem s16h_dc_le_stabSub_commSub {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) :
    L ≤ stabSub (commSub (⊤ : Subgroup W) L) := fun _ hg =>
  StabLat.mem_stabSub_commSub (mem_stabSub.2 fun _ => by simp) (Subgroup.le_normalizer hg)

theorem s16h_dc_le_commutator {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (ht2 : t ^ 2 = 1)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3) {p r m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : (p = 3 ∧ m = 2) ∨ (p = 7 ∧ m = 3)) (hr : 2 ≤ r) (hpr : ¬ (p = 3 ∧ r = 2))
    (hLA : L ≤ A)
    (hLn : ∀ g ∈ A ⊓ stabSub (commSub (⊤ : Subgroup W) L),
      L.map (MulAut.conj g).toMonoidHom = L)
    (hfaith : ∀ l ∈ L, (∀ u ∈ commSub (⊤ : Subgroup W) L, l u = u) → l = 1)
    (hE : IsElemAbelianOfRank p r ↥L) (hLt : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥)
    (hD : DeltaSym A t (commSub (⊤ : Subgroup W) L) r m) : L ≤ ⁅A, A⁆ := by
  obtain ⟨Δ, hinj, hrk, hind, hsup, σ, hσsurj, hσact, ht, hswap, hfix⟩ := hD
  refine s16h_dc_core hp hp2 hr hpr hLA (s16h_dc_le_stabSub_commSub L) hLn hfaith hE hLt hsup
    hσsurj hσact ht hswap fun i hi x hx => ?_
  by_cases h2 : 2 < r
  · exact hfix h2 i hi x hx
  · obtain rfl : r = 2 := by omega
    have hm3 : m = 3 := by
      rcases hm with ⟨hp3, -⟩ | ⟨-, h3⟩
      · exact absurd ⟨hp3, rfl⟩ hpr
      · exact h3
    exact s16h_dc_fixed_of_rank hW ht2 htr hinj hind (fun j => (hrk j).trans hm3) hswap
      (fun j => hσact ⟨t, ht⟩ j) i hi x hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
