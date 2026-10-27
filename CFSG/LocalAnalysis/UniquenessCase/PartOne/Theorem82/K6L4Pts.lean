module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open Subgroup

section Loc

variable {Y : Type} [Group Y] [Finite Y] (r : ℕ)

@[expose] def Loc1 (C : Subgroup Y) : Prop :=
  (Nat.card C).factorization r = 2 ∧ pRank r C = 2 ∧
    ∃ K : Subgroup Y, K ≤ C ∧ ¬ IsSolvable ↥K ∧ ⁅K, K⁆ = K ∧
      Nat.card K = r ^ 2 * (r ^ 2 - 1) ^ 2 / 2 ∧
      ∀ N : Subgroup Y, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) → N = ⊥

@[expose] def Loc2 (C : Subgroup Y) : Prop :=
  (Nat.card C).factorization r = 1

@[expose] def Loc3 (C : Subgroup Y) : Prop :=
  (Nat.card C).factorization r = 3 ∧ pRank r C = 2 ∧
    ∃ K : Subgroup Y, K ≤ C ∧ ¬ IsSolvable ↥K ∧
      ∀ N : Subgroup Y, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) →
        N ≤ centralizer (K : Set Y)

private theorem Loc_conj_map_comap_inf (M N : Subgroup Y) (g : Y)
    (hN : N ≤ M.map (MulAut.conj g).toMonoidHom) :
    (N.comap (MulAut.conj g).toMonoidHom ⊓ M).map (MulAut.conj g).toMonoidHom = N := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact Subgroup.mem_comap.mp hy.1
  · intro x hx
    obtain ⟨y, hyM, hyx⟩ := Subgroup.mem_map.mp (hN hx)
    rw [Subgroup.mem_map]
    refine ⟨y, ⟨?_, hyM⟩, hyx⟩
    exact Subgroup.mem_comap.mpr (hyx ▸ hx)

private theorem Loc_conj_pRank (C : Subgroup Y) (g : Y) :
    pRank r (C.map (MulAut.conj g).toMonoidHom) = pRank r C := by
  unfold pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hE, hEab, hEcard⟩
    refine ⟨E.comap (MulAut.conj g).toMonoidHom ⊓ C, inf_le_right, ?_, ?_⟩
    · refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun a ha => ?_⟩
      · apply Subtype.ext
        change (a : Y) * (b : Y) = (b : Y) * (a : Y)
        exact (MulAut.conj g).injective (by
          rw [map_mul, map_mul]
          exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨_, Subgroup.mem_comap.mp a.2.1⟩
            ⟨_, Subgroup.mem_comap.mp b.2.1⟩))
      · exact (MulAut.conj g).injective (by
          rw [map_pow, map_one]
          exact hEab.2 _ (Subgroup.mem_comap.mp ha.1))
    · have hmap := Loc_conj_map_comap_inf C E g hE
      have hcard : Nat.card ↥(E.comap (MulAut.conj g).toMonoidHom ⊓ C) = Nat.card ↥E := by
        have h := Subgroup.card_map_of_injective
          (K := E.comap (MulAut.conj g).toMonoidHom ⊓ C)
          (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
        rw [hmap] at h
        exact h.symm
      rw [hcard, hEcard]
  · rintro ⟨E, hE, hEab, hEcard⟩
    refine ⟨E.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hE, ?_, ?_⟩
    · refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun a ha => ?_⟩
      · obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.mp a.2
        obtain ⟨y, hy, hyφ⟩ := Subgroup.mem_map.mp b.2
        apply Subtype.ext
        change (a : Y) * (b : Y) = (b : Y) * (a : Y)
        have hcomm : x * y = y * x :=
          congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
        rw [← hxφ, ← hyφ, ← map_mul, ← map_mul, hcomm]
      · obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.mp ha
        rw [← hxφ, ← map_pow, hEab.2 x hx, map_one]
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective, hEcard]

private theorem Loc_conj_normal_comap_inf (M N : Subgroup Y) (g : Y)
    (hN : (N.subgroupOf (M.map (MulAut.conj g).toMonoidHom)).Normal) :
    ((N.comap (MulAut.conj g).toMonoidHom ⊓ M).subgroupOf M).Normal := by
  refine ⟨fun a ha b => ?_⟩
  have hmem : (MulAut.conj g) ((b : Y) * (a : Y) * (b : Y)⁻¹) ∈ N := by
    have h := hN.conj_mem ⟨(MulAut.conj g) (a : Y), Subgroup.mem_map_of_mem _ a.2⟩
      (Subgroup.mem_comap.mp ha.1) ⟨(MulAut.conj g) (b : Y), Subgroup.mem_map_of_mem _ b.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    convert h using 1
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact ⟨Subgroup.mem_comap.mpr hmem, M.mul_mem (M.mul_mem b.2 a.2) (M.inv_mem b.2)⟩

theorem centralizer_conj (g x : Y) :
    centralizer ({g * x * g⁻¹} : Set Y) =
      (centralizer ({x} : Set Y)).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  · intro h
    calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group

theorem Loc1.conj {C : Subgroup Y} (h : Loc1 r C) (g : Y) :
    Loc1 r (C.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hcard, hrank, K, hKC, hKns, hKperf, hKcard, hKodd⟩ := h
  refine ⟨?_, ?_, K.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hKC, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hcard]
  · rw [Loc_conj_pRank r C g, hrank]
  · intro hs
    let e : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    haveI : Group.IsSolvable ↥(K.map (MulAut.conj g).toMonoidHom) := hs
    exact hKns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · rw [← Subgroup.map_commutator K K (MulAut.conj g).toMonoidHom, hKperf]
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hKcard]
  · intro N hNle hNnorm hNodd
    have hmap := Loc_conj_map_comap_inf K N g hNle
    have hcardN : Nat.card ↥(N.comap (MulAut.conj g).toMonoidHom ⊓ K) = Nat.card ↥N := by
      have h := Subgroup.card_map_of_injective (K := N.comap (MulAut.conj g).toMonoidHom ⊓ K)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      rw [hmap] at h
      exact h.symm
    have hNodd' : Odd (Nat.card ↥(N.comap (MulAut.conj g).toMonoidHom ⊓ K)) := by
      rw [hcardN]
      exact hNodd
    have hnorm := Loc_conj_normal_comap_inf K N g hNnorm
    have hthis := hKodd (N.comap (MulAut.conj g).toMonoidHom ⊓ K) inf_le_right hnorm hNodd'
    rw [← hmap, hthis, Subgroup.map_bot]

theorem Loc2.conj {C : Subgroup Y} (h : Loc2 r C) (g : Y) :
    Loc2 r (C.map (MulAut.conj g).toMonoidHom) := by
  unfold Loc2 at h ⊢
  rwa [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]

theorem Loc3.conj {C : Subgroup Y} (h : Loc3 r C) (g : Y) :
    Loc3 r (C.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hcard, hrank, K, hKC, hKns, hKcent⟩ := h
  refine ⟨?_, ?_, K.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hKC, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hcard]
  · rw [Loc_conj_pRank r C g, hrank]
  · intro hs
    let e : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    haveI : Group.IsSolvable ↥(K.map (MulAut.conj g).toMonoidHom) := hs
    exact hKns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · intro N hNle hNnorm hNodd
    have hmap := Loc_conj_map_comap_inf K N g hNle
    have hcardN : Nat.card ↥(N.comap (MulAut.conj g).toMonoidHom ⊓ K) = Nat.card ↥N := by
      have h := Subgroup.card_map_of_injective (K := N.comap (MulAut.conj g).toMonoidHom ⊓ K)
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      rw [hmap] at h
      exact h.symm
    have hNodd' : Odd (Nat.card ↥(N.comap (MulAut.conj g).toMonoidHom ⊓ K)) := by
      rw [hcardN]
      exact hNodd
    have hnorm := Loc_conj_normal_comap_inf K N g hNnorm
    have hcent := hKcent (N.comap (MulAut.conj g).toMonoidHom ⊓ K) inf_le_right hnorm hNodd'
    calc N = (N.comap (MulAut.conj g).toMonoidHom ⊓ K).map (MulAut.conj g).toMonoidHom :=
          hmap.symm
      _ ≤ (Subgroup.centralizer (K : Set Y)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hcent
      _ ≤ Subgroup.centralizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) := by
          simpa using Subgroup.map_centralizer_le_centralizer_image (K : Set Y)
            (MulAut.conj g).toMonoidHom

end Loc

section Transfer

variable {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 4) K)} {Y : Type} [Group Y]
  [Finite Y] {π : H →* Y}

private theorem transfer8_basic_card_map_mul_card_inf_ker {G N : Type*} [Group G] [Group N]
    (f : G →* N) (S : Subgroup G) :
    Nat.card (S.map f) * Nat.card ↥(S ⊓ f.ker) = Nat.card S := by
  let r := f.domRestrict S
  have kernel_eq : r.ker = (S ⊓ f.ker).subgroupOf S := by
    rw [show r.ker = f.ker.subgroupOf S from rfl, inf_subgroupOf_left]
  have range_eq : r.range = S.map f := MonoidHom.domRestrict_range S f
  have quotient_card := Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv
  have product_eq := r.ker.card_eq_card_quotient_mul_card_subgroup
  rw [quotient_card, kernel_eq, range_eq] at product_eq
  rw [product_eq]
  congr 1
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

private theorem transfer8_odd_map_inf_comap {G N : Type*} [Group G] [Group N]
    (f : G →* N) (S : Subgroup G) (T : Subgroup N) (hT : T ≤ S.map f) :
    (S ⊓ T.comap f).map f = T := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hT hy)
    exact Subgroup.mem_map.mpr ⟨x, ⟨hx, hy⟩, rfl⟩

private theorem transfer8_odd_normal {S : Subgroup H} {N : Subgroup Y}
    (hNnorm : (N.subgroupOf (S.map π)).Normal) :
    ((S ⊓ N.comap π).subgroupOf S).Normal := by
  let g : ↥S →* ↥(S.map π) :=
    (π.comp S.subtype).codRestrict (S.map π) fun x => ⟨x, x.2, rfl⟩
  have hsub : (S ⊓ N.comap π).subgroupOf S = (N.subgroupOf (S.map π)).comap g := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨-, hxN⟩
      exact hxN
    · intro hxN
      exact ⟨x.2, hxN⟩
  rw [hsub]
  exact hNnorm.comap g

theorem transfer8_basic (hπ : TwoQuot π)
    (hker : π.ker = (StatedScalars (Fin 4) K).subgroupOf H) {r : ℕ} {K₁ : Subgroup H}
    (hperf : ⁅K₁, K₁⁆ = K₁) (hns : ¬ IsSolvable K₁) (hcard : Nat.card K₁ = (r * (r ^ 2 - 1)) ^ 2)
    (hz : Nat.card ↥(K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf H) = 2) :
    ¬ IsSolvable ↥(K₁.map π) ∧ ⁅K₁.map π, K₁.map π⁆ = K₁.map π ∧
      Nat.card (K₁.map π) = r ^ 2 * (r ^ 2 - 1) ^ 2 / 2 := by
  have hker2 : Nat.card ↥(K₁ ⊓ π.ker) = 2 := by rw [hker]; exact hz
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    haveI : Group.IsSolvable ↥(K₁.map π) := hs
    apply hns
    haveI : Group.IsSolvable ↥((π.ker).subgroupOf K₁) :=
      Group.isSolvable_of_comm fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp
        (hπ.central (Subgroup.mem_subgroupOf.mp a.2)) ((b : ↥K₁) : H)).symm
    let g : ↥K₁ →* ↥(K₁.map π) :=
      (π.comp K₁.subtype).codRestrict (K₁.map π) fun x => ⟨x, x.2, rfl⟩
    have hfg : g.ker ≤ ((π.ker).subgroupOf K₁).subtype.range := by
      rw [Subgroup.range_subtype]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (MonoidHom.mem_ker.mpr (by
        have hval : (g x : Y) = 1 := congrArg (fun z : ↥(K₁.map π) => (z : Y)) hx
        exact hval))
    exact Group.isSolvable_of_ker_le_range ((π.ker).subgroupOf K₁).subtype g hfg
  · rw [← Subgroup.map_commutator, hperf]
  · have h := transfer8_basic_card_map_mul_card_inf_ker π K₁
    rw [hker2, hcard, mul_pow] at h
    rw [← h]
    exact (Nat.mul_div_cancel _ (show 0 < 2 by norm_num)).symm

theorem transfer8_odd (hπ : TwoQuot π)
    (hker : π.ker = (StatedScalars (Fin 4) K).subgroupOf H) {K₁ : Subgroup H}
    (hz : Nat.card ↥(K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf H) = 2)
    (hN : ∀ N : Subgroup H, N ≤ K₁ → (N.subgroupOf K₁).Normal →
      K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf H ≤ N → Odd (Nat.card N / 2) →
        N ≤ (StatedScalars (Fin 4) K).subgroupOf H) :
    ∀ N : Subgroup Y, N ≤ K₁.map π → (N.subgroupOf (K₁.map π)).Normal →
      Odd (Nat.card N) → N = ⊥ := by
  intro N hNle hNnorm hNodd
  let Nt : Subgroup H := K₁ ⊓ N.comap π
  have hker_le : π.ker ≤ N.comap π := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact N.one_mem
  have hinf : Nt ⊓ π.ker = K₁ ⊓ π.ker := by
    show (K₁ ⊓ N.comap π) ⊓ π.ker = K₁ ⊓ π.ker
    rw [inf_assoc, inf_eq_right.mpr hker_le]
  have hker2 : Nat.card ↥(K₁ ⊓ π.ker) = 2 := by rw [hker]; exact hz
  have hmap : Nt.map π = N := transfer8_odd_map_inf_comap π K₁ N hNle
  have hcard : Nat.card Nt = Nat.card N * 2 := by
    have h := transfer8_basic_card_map_mul_card_inf_ker π Nt
    rw [hmap, hinf, hker2] at h
    exact h.symm
  have hoddNt : Odd (Nat.card Nt / 2) := by
    rw [hcard, Nat.mul_div_cancel _ (show 0 < 2 by norm_num)]
    exact hNodd
  have hnorm : (Nt.subgroupOf K₁).Normal := transfer8_odd_normal hNnorm
  have hZle : K₁ ⊓ (StatedScalars (Fin 4) K).subgroupOf H ≤ Nt := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    show π x ∈ N
    have hxker : x ∈ π.ker := hker.symm ▸ hx.2
    rw [MonoidHom.mem_ker.mp hxker]
    exact N.one_mem
  have hNt : Nt ≤ (StatedScalars (Fin 4) K).subgroupOf H :=
    hN Nt inf_le_left hnorm hZle hoddNt
  have hbot : Nt.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact hker.symm ▸ hNt
  rw [← hmap, hbot]

private theorem transfer9_restrict_injective {K₃ : Subgroup H} (hsc : K₃ ⊓ π.ker = ⊥) :
    Function.Injective ((π.comp K₃.subtype).codRestrict (K₃.map π)
      fun x => ⟨x, x.2, rfl⟩) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hx
    apply Subtype.ext
    have hxπ : π (x : H) = 1 := by
      have hval : (((π.comp K₃.subtype).codRestrict (K₃.map π) _) x : Y) = 1 :=
        congrArg (fun z : ↥(K₃.map π) => (z : Y)) hx
      exact hval
    have hx' : (x : H) ∈ K₃ ⊓ π.ker := ⟨x.2, MonoidHom.mem_ker.mpr hxπ⟩
    rw [hsc] at hx'
    simpa using Subgroup.mem_bot.mp hx'
  · intro hx
    rw [hx, map_one]

private theorem transfer9_odd_normal {K₃ : Subgroup H} (hsc : K₃ ⊓ π.ker = ⊥)
    {N : Subgroup Y} (hNle : N ≤ K₃.map π) (hNnorm : (N.subgroupOf (K₃.map π)).Normal)
    (hNodd : Odd (Nat.card N)) :
    ((K₃ ⊓ N.comap π).subgroupOf K₃).Normal ∧
      Odd (Nat.card ↥(K₃ ⊓ N.comap π)) ∧ (K₃ ⊓ N.comap π).map π = N := by
  have hker_le : π.ker ≤ N.comap π := by
    intro x hx
    show π x ∈ N
    rw [MonoidHom.mem_ker.mp hx]
    exact N.one_mem
  have hmap : (K₃ ⊓ N.comap π).map π = N := transfer8_odd_map_inf_comap π K₃ N hNle
  have hinf : (K₃ ⊓ N.comap π) ⊓ π.ker = ⊥ := by
    rw [inf_assoc, inf_eq_right.mpr hker_le, hsc]
  have hcardbot : Nat.card ↥((K₃ ⊓ N.comap π) ⊓ π.ker) = 1 := by rw [hinf]; simp
  have hcard : Nat.card ↥(K₃ ⊓ N.comap π) = Nat.card N := by
    have h := transfer8_basic_card_map_mul_card_inf_ker π (K₃ ⊓ N.comap π)
    rw [hmap, hcardbot] at h
    simpa using h.symm
  exact ⟨transfer8_odd_normal hNnorm, by rw [hcard]; exact hNodd, hmap⟩

theorem transfer9 (hπ : TwoQuot π) (hker : π.ker = (StatedScalars (Fin 4) K).subgroupOf H)
    {K₃ : Subgroup H} (hns : ¬ IsSolvable K₃)
    (hsc : K₃ ⊓ (StatedScalars (Fin 4) K).subgroupOf H = ⊥)
    (hN : ∀ N : Subgroup H, N ≤ K₃ → (N.subgroupOf K₃).Normal → Odd (Nat.card N) →
      N ≤ centralizer (K₃ : Set H)) :
    ¬ IsSolvable ↥(K₃.map π) ∧ ∀ N : Subgroup Y, N ≤ K₃.map π →
      (N.subgroupOf (K₃.map π)).Normal → Odd (Nat.card N) →
        N ≤ centralizer ((K₃.map π : Subgroup Y) : Set Y) := by
  have hsc' : K₃ ⊓ π.ker = ⊥ := by rw [hker]; exact hsc
  refine ⟨?_, ?_⟩
  · intro hs
    haveI : Group.IsSolvable ↥(K₃.map π) := hs
    exact hns (Group.isSolvable_of_isSolvable_injective (transfer9_restrict_injective hsc'))
  · intro N hNle hNnorm hNodd
    obtain ⟨hnorm, hodd, hmap⟩ := transfer9_odd_normal hsc' hNle hNnorm hNodd
    have hcentral : K₃ ⊓ N.comap π ≤ centralizer (K₃ : Set H) :=
      hN (K₃ ⊓ N.comap π) inf_le_left hnorm hodd
    calc N = (K₃ ⊓ N.comap π).map π := hmap.symm
      _ ≤ (centralizer (K₃ : Set H)).map π := Subgroup.map_mono hcentral
      _ ≤ centralizer ((K₃.map π : Subgroup Y) : Set Y) := by
            rw [Subgroup.coe_map]
            exact Subgroup.map_centralizer_le_centralizer_image (K₃ : Set H) π

variable {ζ : CubeRoot K} {r : ℕ}

theorem loc1_standard (hπ : TwoQuot π) (hker : π.ker = (StatedScalars (Fin 4) K).subgroupOf H)
    (hstd : D₀ ζ ≤ H) (hr : r.Prime) (h2 : r ≠ 2) (cent : CentFact H ζ r)
    (sub8 : Sub8Fact H ζ r) :
    Loc1 r (centralizer ({π (stdPt ζ hstd ![1, 1, -1, -1])} : Set Y)) := by
  let d : H := stdPt ζ hstd ![1, 1, -1, -1]
  change Loc1 r (centralizer ({π d} : Set Y))
  have hd1 : (d : GL (Fin 4) K) = d₁ ζ := rfl
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    change (d : GL (Fin 4) K) ^ 3 = 1
    rw [hd1]
    exact stdDiagHom_pow_three ζ (Multiplicative.ofAdd ![1, 1, -1, -1])
  unfold Loc1
  rw [TwoQuot.centralizer_map_singleton hπ hd3]
  refine ⟨?_, ?_, ?_⟩
  · rw [TwoQuot.factorization_card_map hπ (Subgroup.centralizer ({d} : Set H)) hr h2]
    exact (cent.1 d hd1).1
  · rw [TwoQuot.pRank_map hπ (Subgroup.centralizer ({d} : Set H)) hr h2]
    exact (cent.1 d hd1).2
  · obtain ⟨K₁, hK₁le, hperf, hns, hcard, hz, hodd⟩ := sub8 d hd1
    have htb := transfer8_basic hπ hker hperf hns hcard hz
    exact ⟨K₁.map π, Subgroup.map_mono hK₁le, htb.1, htb.2.1, htb.2.2,
      transfer8_odd hπ hker hz hodd⟩

theorem loc2_standard (hπ : TwoQuot π) (hstd : D₀ ζ ≤ H) (hr : r.Prime) (h2 : r ≠ 2)
    (cent : CentFact H ζ r) :
    Loc2 r (centralizer ({π (stdPt ζ hstd ![1, -1, 0, 0])} : Set Y)) := by
  let d : H := stdPt ζ hstd ![1, -1, 0, 0]
  change Loc2 r (centralizer ({π d} : Set Y))
  have hd2 : (d : GL (Fin 4) K) = d₂ ζ := rfl
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    change (d : GL (Fin 4) K) ^ 3 = 1
    rw [hd2]
    exact stdDiagHom_pow_three ζ (Multiplicative.ofAdd ![1, -1, 0, 0])
  unfold Loc2
  rw [TwoQuot.centralizer_map_singleton hπ hd3,
    TwoQuot.factorization_card_map hπ (Subgroup.centralizer ({d} : Set H)) hr h2]
  exact cent.2.1 d hd2

theorem loc3_standard (hπ : TwoQuot π) (hker : π.ker = (StatedScalars (Fin 4) K).subgroupOf H)
    (hstd : D₀ ζ ≤ H) (hr : r.Prime) (h2 : r ≠ 2) (cent : CentFact H ζ r)
    (sub9 : Sub9Fact H ζ) :
    Loc3 r (centralizer ({π (stdPt ζ hstd ![1, 1, 1, 0])} : Set Y)) := by
  let d : H := stdPt ζ hstd ![1, 1, 1, 0]
  change Loc3 r (centralizer ({π d} : Set Y))
  have hd3 : (d : GL (Fin 4) K) = d₃ ζ := rfl
  have hd3pow : d ^ 3 = 1 := by
    apply Subtype.ext
    change (d : GL (Fin 4) K) ^ 3 = 1
    rw [hd3]
    exact stdDiagHom_pow_three ζ (Multiplicative.ofAdd ![1, 1, 1, 0])
  unfold Loc3
  rw [TwoQuot.centralizer_map_singleton hπ hd3pow]
  refine ⟨?_, ?_, ?_⟩
  · rw [TwoQuot.factorization_card_map hπ (Subgroup.centralizer ({d} : Set H)) hr h2]
    exact (cent.2.2.1 d hd3).1
  · rw [TwoQuot.pRank_map hπ (Subgroup.centralizer ({d} : Set H)) hr h2]
    exact (cent.2.2.1 d hd3).2
  · obtain ⟨K₃, hK₃le, hns, hsc, hN⟩ := sub9 d hd3
    have ht9 := transfer9 hπ hker hns hsc hN
    exact ⟨K₃.map π, Subgroup.map_mono hK₃le, ht9.1, ht9.2⟩

theorem threePart_standard (hπ : TwoQuot π) (hstd : D₀ ζ ≤ H) (r : ℕ) (cent : CentFact H ζ r) :
    (Nat.card (centralizer ((((D₀ ζ).subgroupOf H).map π : Subgroup Y) : Set Y))).factorization 3 =
      (Nat.card (centralizer ({π (stdPt ζ hstd ![1, -1, 0, 0])} : Set Y))).factorization 3 := by
  let d : H := stdPt ζ hstd ![1, -1, 0, 0]
  have hd2 : (d : GL (Fin 4) K) = d₂ ζ := rfl
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    change (d : GL (Fin 4) K) ^ 3 = 1
    rw [hd2]
    exact stdDiagHom_pow_three ζ (Multiplicative.ofAdd ![1, -1, 0, 0])
  have hS : ∀ s ∈ (D₀ ζ).subgroupOf H, s ^ 3 = 1 := by
    intro s hs
    apply Subtype.ext
    change (s : GL (Fin 4) K) ^ 3 = 1
    exact D₀_pow_three ζ hs
  change (Nat.card (centralizer
    ((((D₀ ζ).subgroupOf H).map π : Subgroup Y) : Set Y))).factorization 3 =
    (Nat.card (centralizer ({π d} : Set Y))).factorization 3
  rw [TwoQuot.centralizer_map hπ hS,
    TwoQuot.factorization_card_map hπ
      (Subgroup.centralizer (((D₀ ζ).subgroupOf H : Subgroup H) : Set H)) Nat.prime_three
      (by norm_num),
    TwoQuot.centralizer_map_singleton hπ hd3,
    TwoQuot.factorization_card_map hπ (Subgroup.centralizer ({d} : Set H)) Nat.prime_three
      (by norm_num)]
  exact cent.2.2.2 d hd2

end Transfer

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
