module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Uc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private abbrev uc22s2122npQ (N S : Subgroup G) [h : (S.subgroupOf N).Normal] : Type :=
  ↥N ⧸ S.subgroupOf N

private abbrev uc22s2122npMk (N S : Subgroup G) [h : (S.subgroupOf N).Normal] :
    ↥N →* uc22s2122npQ N S :=
  QuotientGroup.mk' (S.subgroupOf N)

private theorem uc22s2122np_quot_rel {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {k : ℕ} {x y : G} (hSN : S ≤ N) (hxN : x ∈ N) (hyN : y ∈ N)
    (hk : x * y * x⁻¹ * (y ^ k)⁻¹ ∈ S) :
    uc22s2122npMk N S ⟨x, hxN⟩ * uc22s2122npMk N S ⟨y, hyN⟩ *
        (uc22s2122npMk N S ⟨x, hxN⟩)⁻¹ = (uc22s2122npMk N S ⟨y, hyN⟩) ^ k := by
  have hzN : x * y * x⁻¹ * (y ^ k)⁻¹ ∈ N := hSN hk
  have hq1 : uc22s2122npMk N S ⟨x * y * x⁻¹ * (y ^ k)⁻¹, hzN⟩ = 1 := by
    change (QuotientGroup.mk' (S.subgroupOf N)) _ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  have hprod : uc22s2122npMk N S ⟨x * y * x⁻¹ * (y ^ k)⁻¹, hzN⟩ =
      uc22s2122npMk N S ⟨x, hxN⟩ * uc22s2122npMk N S ⟨y, hyN⟩ *
        (uc22s2122npMk N S ⟨x, hxN⟩)⁻¹ * (uc22s2122npMk N S ⟨y, hyN⟩ ^ k)⁻¹ := by
    change (QuotientGroup.mk' (S.subgroupOf N)) ⟨x * y * x⁻¹ * (y ^ k)⁻¹, hzN⟩ =
      (QuotientGroup.mk' (S.subgroupOf N)) ⟨x, hxN⟩ *
        (QuotientGroup.mk' (S.subgroupOf N)) ⟨y, hyN⟩ *
        ((QuotientGroup.mk' (S.subgroupOf N)) ⟨x, hxN⟩)⁻¹ *
        ((QuotientGroup.mk' (S.subgroupOf N)) ⟨y, hyN⟩ ^ k)⁻¹
    rw [← map_pow, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [hprod] at hq1
  exact mul_inv_eq_one.1 hq1

private theorem uc22s2122np_quot_pow_one {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {s : ℕ} {x : G} (hxN : x ∈ N) (hxs : x ^ s = 1) :
    (uc22s2122npMk N S ⟨x, hxN⟩) ^ s = 1 := by
  rw [← map_pow]
  have h1 : (⟨x, hxN⟩ : ↥N) ^ s = 1 := by
    ext
    simpa using hxs
  rw [h1, map_one]

private theorem uc22s2122np_quot_pow_mem_one {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {s : ℕ} {y : G} (hSN : S ≤ N) (hyN : y ∈ N) (hys : y ^ s ∈ S) :
    (uc22s2122npMk N S ⟨y, hyN⟩) ^ s = 1 := by
  rw [← map_pow]
  change (QuotientGroup.mk' (S.subgroupOf N)) ((⟨y, hyN⟩ : ↥N) ^ s) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h1 : ((⟨y, hyN⟩ : ↥N) ^ s : ↥N) = ⟨y ^ s, hSN hys⟩ := by
    ext
    rfl
  rw [h1]
  exact hys

private theorem uc22s2122np_quot_iterate {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {s k : ℕ} {x y : G} (hxN : x ∈ N) (hyN : y ∈ N)
    (hxq : (uc22s2122npMk N S ⟨x, hxN⟩) ^ s = 1)
    (hrel : uc22s2122npMk N S ⟨x, hxN⟩ * uc22s2122npMk N S ⟨y, hyN⟩ *
        (uc22s2122npMk N S ⟨x, hxN⟩)⁻¹ = (uc22s2122npMk N S ⟨y, hyN⟩) ^ k) :
    (uc22s2122npMk N S ⟨y, hyN⟩) ^ (k ^ s) = uc22s2122npMk N S ⟨y, hyN⟩ := by
  let xq := uc22s2122npMk N S ⟨x, hxN⟩
  let yq := uc22s2122npMk N S ⟨y, hyN⟩
  have hxq' : xq ^ s = 1 := hxq
  have hrel' : xq * yq * xq⁻¹ = yq ^ k := hrel
  have hj : ∀ j : ℕ, xq ^ j * yq * (xq ^ j)⁻¹ = yq ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc xq ^ (j + 1) * yq * (xq ^ (j + 1))⁻¹
          = xq * (xq ^ j * yq * (xq ^ j)⁻¹) * xq⁻¹ := by rw [pow_succ']; group
        _ = xq * (yq ^ (k ^ j)) * xq⁻¹ := by rw [ih]
        _ = (xq * yq * xq⁻¹) ^ (k ^ j) := by rw [conj_pow]
        _ = (yq ^ k) ^ (k ^ j) := by rw [hrel']
        _ = yq ^ (k ^ (j + 1)) := by rw [← pow_mul, pow_succ']
  have h1 := hj s
  rw [hxq', one_mul, inv_one, mul_one] at h1
  simpa [xq, yq] using h1.symm

private theorem uc22s2122np_mem_of_quot_eq_one {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {g : G} (hgN : g ∈ N) (h : uc22s2122npMk N S ⟨g, hgN⟩ = 1) : g ∈ S := by
  change (QuotientGroup.mk' (S.subgroupOf N)) ⟨g, hgN⟩ = 1 at h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  exact h

private theorem uc22s2122np_quot_comm {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {x y : G} (hxN : x ∈ N) (hyN : y ∈ N) (hN : x * y * x⁻¹ * y⁻¹ ∈ N)
    (h3 : uc22s2122npMk N S ⟨x, hxN⟩ * uc22s2122npMk N S ⟨y, hyN⟩ *
        (uc22s2122npMk N S ⟨x, hxN⟩)⁻¹ * (uc22s2122npMk N S ⟨y, hyN⟩)⁻¹ = 1) :
    uc22s2122npMk N S ⟨x * y * x⁻¹ * y⁻¹, hN⟩ = 1 := by
  have hsplit : uc22s2122npMk N S ⟨x * y * x⁻¹ * y⁻¹, hN⟩ =
      uc22s2122npMk N S ⟨x, hxN⟩ * uc22s2122npMk N S ⟨y, hyN⟩ *
        (uc22s2122npMk N S ⟨x, hxN⟩)⁻¹ * (uc22s2122npMk N S ⟨y, hyN⟩)⁻¹ := by
    change (QuotientGroup.mk' (S.subgroupOf N)) ⟨x * y * x⁻¹ * y⁻¹, hN⟩ =
      (QuotientGroup.mk' (S.subgroupOf N)) ⟨x, hxN⟩ *
        (QuotientGroup.mk' (S.subgroupOf N)) ⟨y, hyN⟩ *
        ((QuotientGroup.mk' (S.subgroupOf N)) ⟨x, hxN⟩)⁻¹ *
        ((QuotientGroup.mk' (S.subgroupOf N)) ⟨y, hyN⟩)⁻¹
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [hsplit]
  exact h3

private theorem uc22s2122np_quot_eq_one_of_mem {N S : Subgroup G}
    [hS₀ : (S.subgroupOf N).Normal] {g : G} (hgN : g ∈ N) (hgS : g ∈ S) :
    uc22s2122npMk N S ⟨g, hgN⟩ = 1 := by
  change (QuotientGroup.mk' (S.subgroupOf N)) ⟨g, hgN⟩ = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hgS

theorem uc22s2122np_comm_mod_of_pow {L S : Subgroup G} {a s : ℕ} (hS : IsSylowOf 2 S L)
    (hX : IsSp4 (Bar2 L) a) (hs : s.Prime) (hs2 : s ≠ 2)
    {x : G} (hxL : x ∈ normalizer (L : Set G)) (hxS : x ∈ normalizer (S : Set G))
    (hxs : x ^ s = 1) {y : G} (hyL : y ∈ L) (hyS : y ∈ normalizer (S : Set G))
    (hys : y ^ s ∈ S) : x * y * x⁻¹ * y⁻¹ ∈ S := by
  classical
  haveI : Fact s.Prime := ⟨hs⟩
  obtain ⟨k, hk⟩ := uc22p218d_exists_pow_conj_mem_sp4 hS hX hxL hxS
    (hs.odd_of_ne_two hs2) hxs
  let N : Subgroup G := normalizer (S : Set G)
  have hSN : S ≤ N := fun z hz => Subgroup.le_normalizer hz
  have hS₀ : (S.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).2 le_rfl
  letI : (S.subgroupOf N).Normal := hS₀
  have hxq := uc22s2122np_quot_pow_one (N := N) (S := S) hxS hxs
  have hyq := uc22s2122np_quot_pow_mem_one (N := N) (S := S) hSN hyS hys
  have hrel := uc22s2122np_quot_rel (N := N) (S := S) hSN hxS hyS (hk y hyL hyS)
  have hA := uc22s2122np_quot_iterate (N := N) (S := S) hxS hyS hxq hrel
  have hmod : k ^ s ≡ k [MOD s] := by
    refine (ZMod.natCast_eq_natCast_iff (k ^ s) k s).1 ?_
    rw [Nat.cast_pow]
    exact ZMod.pow_card (k : ZMod s)
  have h2 : (uc22s2122npMk N S ⟨y, hyS⟩) ^ (k ^ s) =
      (uc22s2122npMk N S ⟨y, hyS⟩) ^ k :=
    pow_eq_pow_iff_modEq.2 (hmod.of_dvd (orderOf_dvd_of_pow_eq_one hyq))
  have hyk : (uc22s2122npMk N S ⟨y, hyS⟩) ^ k = uc22s2122npMk N S ⟨y, hyS⟩ := by
    rw [← h2]
    exact hA
  have h3 : uc22s2122npMk N S ⟨x, hxS⟩ * uc22s2122npMk N S ⟨y, hyS⟩ *
      (uc22s2122npMk N S ⟨x, hxS⟩)⁻¹ * (uc22s2122npMk N S ⟨y, hyS⟩)⁻¹ = 1 := by
    rw [hrel, hyk, mul_inv_cancel]
  have hN : x * y * x⁻¹ * y⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem hxS hyS) (N.inv_mem hxS)) (N.inv_mem hyS)
  exact uc22s2122np_mem_of_quot_eq_one hN (uc22s2122np_quot_comm hxS hyS hN h3)

def uc22s2122npWSet (L S : Subgroup G) (s : ℕ) : Set G :=
  {x | x ∈ L ∧ x ∈ normalizer (S : Set G) ∧ x ^ s = 1}

abbrev uc22s2122npV (L S : Subgroup G) (s : ℕ) : Subgroup G :=
  S ⊔ Subgroup.closure (uc22s2122npWSet L S s)

theorem uc22s2122npV_le {L S : Subgroup G} {s : ℕ} (hS : IsSylowOf 2 S L) :
    uc22s2122npV L S s ≤ L :=
  sup_le hS.le ((Subgroup.closure_le _).2 fun _ hx => hx.1)

theorem uc22s2122npV_le_normalizer {L S : Subgroup G} {s : ℕ} :
    uc22s2122npV L S s ≤ normalizer (S : Set G) :=
  sup_le (fun _ hx => Subgroup.le_normalizer hx)
    ((Subgroup.closure_le _).2 fun _ hx => hx.2.1)

theorem uc22s2122npV_mem {L S : Subgroup G} {s : ℕ} {x : G} (hxL : x ∈ L)
    (hxS : x ∈ normalizer (S : Set G)) (hxs : x ^ s = 1) :
    x ∈ uc22s2122npV L S s :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hxL, hxS, hxs⟩)

private theorem uc22s2122npWSet_conj {L S : Subgroup G} {s : ℕ} {g x : G}
    (hgL : g ∈ normalizer (L : Set G)) (hgS : g ∈ normalizer (S : Set G))
    (hx : x ∈ uc22s2122npWSet L S s) : g * x * g⁻¹ ∈ uc22s2122npWSet L S s := by
  obtain ⟨hxL, hxS, hxs⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hgL
    exact (hgL x).1 hxL
  · exact (normalizer (S : Set G)).mul_mem
      ((normalizer (S : Set G)).mul_mem hgS hxS) ((normalizer (S : Set G)).inv_mem hgS)
  · rw [conj_pow, hxs, mul_one, mul_inv_cancel]

private theorem uc22s2122np_closure_normalizer {L S : Subgroup G} {s : ℕ} {g : G}
    (hgen : ∀ x ∈ uc22s2122npWSet L S s, g * x * g⁻¹ ∈ uc22s2122npWSet L S s)
    (hgen' : ∀ x ∈ uc22s2122npWSet L S s, g⁻¹ * x * g ∈ uc22s2122npWSet L S s) :
    g ∈ normalizer (Subgroup.closure (uc22s2122npWSet L S s) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hgen y hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hgen' x hx, ?_⟩
    change (MulAut.conj g) (g⁻¹ * x * g) = x
    rw [MulAut.conj_apply]
    group

theorem uc22s2122npV_le_normalizer_of_mem {L S : Subgroup G} {s : ℕ} {g : G}
    (hgL : g ∈ normalizer (L : Set G)) (hgS : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (uc22s2122npV L S s : Set G) := by
  have hgen : ∀ x ∈ uc22s2122npWSet L S s, g * x * g⁻¹ ∈ uc22s2122npWSet L S s :=
    fun x hx => uc22s2122npWSet_conj hgL hgS hx
  have hgen' : ∀ x ∈ uc22s2122npWSet L S s, g⁻¹ * x * g ∈ uc22s2122npWSet L S s :=
    fun x hx => by
      simpa only [inv_inv] using uc22s2122npWSet_conj
        ((normalizer (L : Set G)).inv_mem hgL) ((normalizer (S : Set G)).inv_mem hgS) hx
  have hcl := uc22s2122np_closure_normalizer hgen hgen'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf ⟨hgS, hcl⟩ x hx
  · intro hx
    have hinv : g⁻¹ ∈ normalizer (S : Set G) ⊓
        normalizer (Subgroup.closure (uc22s2122npWSet L S s) : Set G) :=
      ⟨(normalizer (S : Set G)).inv_mem hgS,
        (normalizer (Subgroup.closure (uc22s2122npWSet L S s) : Set G)).inv_mem hcl⟩
    have h := Subgroup.conj_mem_sup_of_mem_inf_normalizer_of_mem_inf hinv
      (g * x * g⁻¹) hx
    have h' : g⁻¹ * (g * x * g⁻¹) * g ∈
        S ⊔ Subgroup.closure (uc22s2122npWSet L S s) := by
      simpa only [inv_inv] using h
    have he : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [he] at h'
    exact h'

private def uc22s2122npT' (N S : Subgroup G) [h : (S.subgroupOf N).Normal] (T : Set G) :
    Set (uc22s2122npQ N S) :=
  {y | ∃ x : ↥N, (x : G) ∈ T ∧ y = uc22s2122npMk N S x}

private theorem uc22s2122np_closure_image {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {T : Set G} {s : ℕ} (hSN : S ≤ N) (hTN : ∀ x ∈ T, x ∈ N)
    (hTpow : ∀ x ∈ T, x ^ s ∈ S)
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ S) :
    (∀ y ∈ uc22s2122npT' N S T, y ^ s = 1) ∧ (uc22s2122npT' N S T).Pairwise Commute := by
  constructor
  · rintro y ⟨x, hxT, rfl⟩
    exact uc22s2122np_quot_pow_mem_one (N := N) (S := S) hSN x.2 (hTpow x hxT)
  · intro y hy z hz _
    obtain ⟨x, hxT, rfl⟩ := hy
    obtain ⟨w, hwT, rfl⟩ := hz
    have hgN : x.1 * w.1 * x.1⁻¹ * w.1⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem x.2 w.2) (N.inv_mem x.2)) (N.inv_mem w.2)
    have h1 : uc22s2122npMk N S ⟨x.1 * w.1 * x.1⁻¹ * w.1⁻¹, hgN⟩ = 1 :=
      uc22s2122np_quot_eq_one_of_mem hgN (hTcomm x.1 hxT w.1 hwT)
    have hsplit : uc22s2122npMk N S ⟨x.1 * w.1 * x.1⁻¹ * w.1⁻¹, hgN⟩ =
        uc22s2122npMk N S x * uc22s2122npMk N S w *
          (uc22s2122npMk N S x)⁻¹ * (uc22s2122npMk N S w)⁻¹ := by
      change (QuotientGroup.mk' (S.subgroupOf N)) ⟨x.1 * w.1 * x.1⁻¹ * w.1⁻¹, hgN⟩ =
        (QuotientGroup.mk' (S.subgroupOf N)) x * (QuotientGroup.mk' (S.subgroupOf N)) w *
          ((QuotientGroup.mk' (S.subgroupOf N)) x)⁻¹ *
          ((QuotientGroup.mk' (S.subgroupOf N)) w)⁻¹
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    have h2 : uc22s2122npMk N S x * uc22s2122npMk N S w *
        (uc22s2122npMk N S x)⁻¹ * (uc22s2122npMk N S w)⁻¹ = 1 := by
      rw [← hsplit]
      exact h1
    have h3 : uc22s2122npMk N S x * uc22s2122npMk N S w * (uc22s2122npMk N S x)⁻¹ =
        uc22s2122npMk N S w := mul_inv_eq_one.1 h2
    calc uc22s2122npMk N S x * uc22s2122npMk N S w
        = uc22s2122npMk N S x * uc22s2122npMk N S w * (uc22s2122npMk N S x)⁻¹ *
          uc22s2122npMk N S x := by group
      _ = uc22s2122npMk N S w * uc22s2122npMk N S x := by rw [h3]

private theorem uc22s2122np_closure_lift {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {T : Set G} {s : ℕ} (hTN : ∀ x ∈ T, x ∈ N)
    (hT'pow : ∀ y ∈ uc22s2122npT' N S T, y ^ s = 1)
    (hT'comm : (uc22s2122npT' N S T).Pairwise Commute) :
    ∃ A : Subgroup (uc22s2122npQ N S), IsMulCommutative A ∧ (∀ y ∈ A, y ^ s = 1) ∧
      ∀ u ∈ Subgroup.closure T, ∃ nu : ↥N, uc22s2122npMk N S nu ∈ A ∧ (nu : G) = u := by
  classical
  let q := uc22s2122npMk N S
  let A : Subgroup (uc22s2122npQ N S) := Subgroup.closure (uc22s2122npT' N S T)
  have hAcomm : IsMulCommutative A := Subgroup.isMulCommutative_closure hT'comm
  have hApow : ∀ y ∈ A, y ^ s = 1 := fun y hy =>
    CFSG.AGLEmbeddingD2.AltFiveRankTools.pow_eq_one_of_mem_closure_of_pairwise_commute
      hT'comm hT'pow hy
  have hTP : T ⊆ (A.comap q).map N.subtype := by
    intro x hx
    exact ⟨⟨x, hTN x hx⟩, Subgroup.subset_closure ⟨⟨x, hTN x hx⟩, hx, rfl⟩, rfl⟩
  have hclP : Subgroup.closure T ≤ (A.comap q).map N.subtype :=
    (Subgroup.closure_le _).2 hTP
  refine ⟨A, hAcomm, hApow, fun u hu => ?_⟩
  obtain ⟨nu, hnuA, hnu⟩ := Subgroup.mem_map.1 (hclP hu)
  exact ⟨nu, hnuA, hnu⟩

private theorem uc22s2122np_closure_pow {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {T : Set G} {s : ℕ} {A : Subgroup (uc22s2122npQ N S)}
    (hApow : ∀ y ∈ A, y ^ s = 1)
    (hlift : ∀ u ∈ Subgroup.closure T, ∃ nu : ↥N, uc22s2122npMk N S nu ∈ A ∧ (nu : G) = u)
    {u : G} (hu : u ∈ Subgroup.closure T) : u ^ s ∈ S := by
  obtain ⟨nu, hnuA, hnu⟩ := hlift u hu
  have h1 : uc22s2122npMk N S (nu ^ s) = 1 := by
    rw [map_pow]
    exact hApow nu hnuA
  have h2 : (nu : G) ^ s ∈ S :=
    uc22s2122np_mem_of_quot_eq_one (N := N) (S := S) (N.pow_mem nu.2 s) h1
  simpa [hnu] using h2

private theorem uc22s2122np_closure_comm {N S : Subgroup G} [hS₀ : (S.subgroupOf N).Normal]
    {T : Set G} {A : Subgroup (uc22s2122npQ N S)} (hAcomm : IsMulCommutative A)
    (hlift : ∀ u ∈ Subgroup.closure T, ∃ nu : ↥N, uc22s2122npMk N S nu ∈ A ∧ (nu : G) = u)
    {u v : G} (hu : u ∈ Subgroup.closure T) (hv : v ∈ Subgroup.closure T) :
    u * v * u⁻¹ * v⁻¹ ∈ S := by
  obtain ⟨nu, hnuA, hnu⟩ := hlift u hu
  obtain ⟨nv, hnvA, hnv⟩ := hlift v hv
  have hcomm : uc22s2122npMk N S nu * uc22s2122npMk N S nv =
      uc22s2122npMk N S nv * uc22s2122npMk N S nu :=
    congrArg Subtype.val (hAcomm.is_comm.comm ⟨_, hnuA⟩ ⟨_, hnvA⟩)
  have hq : uc22s2122npMk N S (nu * nv * nu⁻¹ * nv⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hS := uc22s2122np_mem_of_quot_eq_one (N := N)
    ((nu * nv * nu⁻¹ * nv⁻¹ : ↥N).2) hq
  have he : ((nu * nv * nu⁻¹ * nv⁻¹ : ↥N) : G) = u * v * u⁻¹ * v⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hnu, hnv]
  rwa [he] at hS

theorem uc22s2122np_closure_mod {S : Subgroup G} {T : Set G} {s : ℕ}
    (hTN : ∀ x ∈ T, x ∈ normalizer (S : Set G))
    (hTpow : ∀ x ∈ T, x ^ s ∈ S)
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ S) :
    ∀ u ∈ Subgroup.closure T, ∀ v ∈ Subgroup.closure T,
      u * v * u⁻¹ * v⁻¹ ∈ S ∧ u ^ s ∈ S := by
  classical
  let N : Subgroup G := normalizer (S : Set G)
  have hSN : S ≤ N := fun z hz => Subgroup.le_normalizer hz
  have hS₀ : (S.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).2 le_rfl
  letI : (S.subgroupOf N).Normal := hS₀
  obtain ⟨hT'pow, hT'comm⟩ := uc22s2122np_closure_image hSN hTN hTpow hTcomm
  obtain ⟨A, hAcomm, hApow, hlift⟩ := uc22s2122np_closure_lift hTN hT'pow hT'comm
  intro u hu v hv
  exact ⟨uc22s2122np_closure_comm hAcomm hlift hu hv,
    uc22s2122np_closure_pow hApow hlift hu⟩

private theorem uc22s2122npV_sup_zpowers_eq_closure {L S : Subgroup G} {s : ℕ} {b : G} :
    uc22s2122npV L S s ⊔ zpowers b =
      Subgroup.closure ((S : Set G) ∪ uc22s2122npWSet L S s ∪ {b}) := by
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · intro x hx
        exact Subgroup.subset_closure
          (k := (S : Set G) ∪ uc22s2122npWSet L S s ∪ {b}) (Or.inl (Or.inl hx))
      · exact Subgroup.closure_mono (by
          intro x hx
          exact Or.inl (Or.inr hx))
    · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure
        (k := (S : Set G) ∪ uc22s2122npWSet L S s ∪ {b}) (Or.inr rfl))
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rw [Set.mem_union, Set.mem_union, Set.mem_singleton_iff] at hx
    rcases hx with (hxS | hxG) | hxb
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hxS)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure hxG))
    · rw [hxb]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)

private theorem uc22s2122np_set_normalizer {L S : Subgroup G} {s : ℕ} {b : G}
    (hbS : b ∈ normalizer (S : Set G)) :
    ∀ x ∈ ((S : Set G) ∪ uc22s2122npWSet L S s ∪ {b}), x ∈ normalizer (S : Set G) := by
  intro x hx
  rw [Set.mem_union, Set.mem_union, Set.mem_singleton_iff] at hx
  rcases hx with (hxS | hxG) | hxb
  · exact Subgroup.le_normalizer hxS
  · exact hxG.2.1
  · rwa [hxb]

private theorem uc22s2122np_set_pow {L S : Subgroup G} {s : ℕ} {b : G} (hbs : b ^ s = 1) :
    ∀ x ∈ ((S : Set G) ∪ uc22s2122npWSet L S s ∪ {b}), x ^ s ∈ S := by
  intro x hx
  rw [Set.mem_union, Set.mem_union, Set.mem_singleton_iff] at hx
  rcases hx with (hxS | hxG) | hxb
  · exact S.pow_mem hxS s
  · rw [hxG.2.2]
    exact S.one_mem
  · rw [hxb, hbs]
    exact S.one_mem

private theorem uc22s2122np_pow_comm_normalizer {S : Subgroup G} {x y : G}
    (hx : x ∈ S) (hy : y ∈ normalizer (S : Set G)) : x * y * x⁻¹ * y⁻¹ ∈ S := by
  rw [Subgroup.mem_normalizer_iff] at hy
  have h1 : y * x⁻¹ * y⁻¹ ∈ S := (hy x⁻¹).1 (S.inv_mem hx)
  have he : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [he]
  exact S.mul_mem hx h1

private theorem uc22s2122np_set_comm_of_mem {L S : Subgroup G} {s : ℕ} {b x : G}
    (hbS : b ∈ normalizer (S : Set G)) (hxS : x ∈ S) :
    ∀ y ∈ ((S : Set G) ∪ uc22s2122npWSet L S s ∪ {b}), x * y * x⁻¹ * y⁻¹ ∈ S := by
  intro y hy
  rw [Set.mem_union, Set.mem_union, Set.mem_singleton_iff] at hy
  rcases hy with (hyS | hyG) | hyb
  · exact uc22s2122np_pow_comm_normalizer hxS (Subgroup.le_normalizer hyS)
  · exact uc22s2122np_pow_comm_normalizer hxS hyG.2.1
  · rw [hyb]
    exact uc22s2122np_pow_comm_normalizer hxS hbS

private theorem uc22s2122np_set_comm {L S : Subgroup G} {a s : ℕ} (hS : IsSylowOf 2 S L)
    (hX : IsSp4 (Bar2 L) a) (hs : s.Prime) (hs2 : s ≠ 2)
    {b : G} (hbNL : b ∈ normalizer (L : Set G)) (hbS : b ∈ normalizer (S : Set G))
    (hbs : b ^ s = 1) :
    ∀ x ∈ ((S : Set G) ∪ uc22s2122npWSet L S s ∪ {b}),
      ∀ y ∈ ((S : Set G) ∪ uc22s2122npWSet L S s ∪ {b}), x * y * x⁻¹ * y⁻¹ ∈ S := by
  intro x hx y hy
  rw [Set.mem_union, Set.mem_union, Set.mem_singleton_iff] at hx
  rw [Set.mem_union, Set.mem_union, Set.mem_singleton_iff] at hy
  rcases hx with (hxS | hxG) | hxb
  · exact uc22s2122np_set_comm_of_mem hbS hxS y hy
  · rcases hy with (hyS | hyG) | hyb
    · have h := uc22s2122np_pow_comm_normalizer hyS hxG.2.1
      have he : y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
      rw [he] at h
      simpa using S.inv_mem h
    · exact uc22s2122np_comm_mod_of_pow hS hX hs hs2
        (Subgroup.le_normalizer hxG.1) hxG.2.1 hxG.2.2 hyG.1 hyG.2.1
        (by rw [hyG.2.2]; exact S.one_mem)
    · rw [hyb]
      have h := uc22s2122np_comm_mod_of_pow hS hX hs hs2 hbNL hbS hbs
        hxG.1 hxG.2.1 (by rw [hxG.2.2]; exact S.one_mem)
      have he : b * x * b⁻¹ * x⁻¹ = (x * b * x⁻¹ * b⁻¹)⁻¹ := by group
      rw [he] at h
      simpa using S.inv_mem h
  · rw [hxb]
    rcases hy with (hyS | hyG) | hyb
    · have h := uc22s2122np_pow_comm_normalizer hyS hbS
      have he : y * b * y⁻¹ * b⁻¹ = (b * y * b⁻¹ * y⁻¹)⁻¹ := by group
      rw [he] at h
      simpa using S.inv_mem h
    · exact uc22s2122np_comm_mod_of_pow hS hX hs hs2 hbNL hbS hbs hyG.1 hyG.2.1
        (by rw [hyG.2.2]; exact S.one_mem)
    · rw [hyb, show b * b * b⁻¹ * b⁻¹ = 1 by group]
      exact S.one_mem

theorem uc22s2122npV_mod {L S : Subgroup G} {a s : ℕ} (hS : IsSylowOf 2 S L)
    (hX : IsSp4 (Bar2 L) a) (hs : s.Prime) (hs2 : s ≠ 2)
    {b : G} (hbNL : b ∈ normalizer (L : Set G)) (hbS : b ∈ normalizer (S : Set G))
    (hbs : b ^ s = 1) :
    ∀ u ∈ uc22s2122npV L S s ⊔ zpowers b, ∀ v ∈ uc22s2122npV L S s ⊔ zpowers b,
      u * v * u⁻¹ * v⁻¹ ∈ S ∧ u ^ s ∈ S := by
  classical
  rw [uc22s2122npV_sup_zpowers_eq_closure (L := L) (S := S) (s := s) (b := b)]
  exact uc22s2122np_closure_mod
    (uc22s2122np_set_normalizer (L := L) (S := S) (s := s) (b := b) hbS)
    (uc22s2122np_set_pow (L := L) (S := S) (s := s) (b := b) hbs)
    (uc22s2122np_set_comm hS hX hs hs2 hbNL hbS hbs)

theorem uc22s2122np_pRank_le_two {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h211 : S21_1 D Ch) (hH : H1930 D) (c : Ctx21 D Ch)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hML : D.M ≤ normalizer (L : Set G))
    {a s : ℕ} (hX : IsSp4 (Bar2 L) a) (ha : Odd a) (hs : s.Prime) (hsa : s ∣ 2 ^ a - 1) :
    CFSG.Open.pRank s D.M ≤ 2 := by
  have ha1 : 1 ≤ a := by
    obtain ⟨k, rfl⟩ := ha
    omega
  have hs2 : s ≠ 2 := uc22p218c_ne_two_of_dvd ha1 hsa
  have hns := UC6S846.not_solvable_of_mem_calC hL
  by_contra h
  exact uc22p218s_not_stronglyEmbedded D Ch h211 hH c hL.1.le hML hX ha hs hs2 hsa
    (UC6S846.sp_of_mem_sig hSg hns (hσ s hs (uc22s218u_seven_le ha hs hsa) (by omega)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
