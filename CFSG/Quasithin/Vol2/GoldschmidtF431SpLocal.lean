module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpTrans

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint

universe u v

section Transport

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {N : Subgroup Mb} {b : ↥N →* G}

theorem mem_subImg_iff_of_injective (hb : Function.Injective b) {X : Subgroup Mb} {x : Mb}
    (hx : x ∈ N) : b ⟨x, hx⟩ ∈ subImg b X ↔ x ∈ X := by
  constructor
  · intro h
    obtain ⟨y, hy, hyX, hyx⟩ := mem_subImg.mp h
    have : (⟨y, hy⟩ : ↥N) = ⟨x, hx⟩ := hb hyx
    have hyx' : y = x := congrArg Subtype.val this
    rwa [← hyx']
  · intro h
    exact mem_subImg_of_mem b hx h

theorem subImg_le_normalizer (b : ↥N →* G) {X Y : Subgroup Mb}
    (h : X ≤ Subgroup.normalizer (Y : Set Mb)) :
    subImg b X ≤ Subgroup.normalizer (subImg b Y : Set G) := by
  have key : ∀ x ∈ subImg b X, ∀ y ∈ subImg b Y, x * y * x⁻¹ ∈ subImg b Y := by
    intro x hx y hy
    obtain ⟨x', hx'N, hx'X, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy'N, hy'Y, rfl⟩ := mem_subImg.mp hy
    have hc : x' * y' * x'⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (h hx'X) y').mp hy'Y
    refine mem_subImg.mpr ⟨x' * y' * x'⁻¹, N.mul_mem (N.mul_mem hx'N hy'N) (N.inv_mem hx'N), hc, ?_⟩
    have : (⟨x' * y' * x'⁻¹, N.mul_mem (N.mul_mem hx'N hy'N) (N.inv_mem hx'N)⟩ : ↥N) =
        ⟨x', hx'N⟩ * ⟨y', hy'N⟩ * ⟨x', hx'N⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key x hx y hy, fun hy => by
    have := key x⁻¹ ((subImg b X).inv_mem hx) _ hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this⟩

end Transport

section LieSide

variable {Mb : Type u} [Group Mb] {T N1 N2 : Subgroup Mb} {I : Finset Mb}

theorem T_le_spN (L : F431SpLie T N1 N2 I) (j : Fin 2) : T ≤ spN N1 N2 j := by
  fin_cases j
  · exact L.W.T_le₁
  · exact L.W.T_le₂

theorem spQ_le [Finite Mb] (L : F431SpLie T N1 N2 I) (j : Fin 2) : spQ N1 N2 j ≤ T :=
  F7.isSylowTwoOf_pCoreOf_le (F7.isSylowTwoOf_mono_right L.W.sylow (T_le_spN L j) le_top)

theorem T_le_normalizer_spQ (L : F431SpLie T N1 N2 I) (j : Fin 2) :
    T ≤ Subgroup.normalizer (spQ N1 N2 j : Set Mb) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => pCoreOf_conj_mem (T_le_spN L j ht) hx, fun hx => by
    have := pCoreOf_conj_mem ((spN N1 N2 j).inv_mem (T_le_spN L j ht)) hx
    rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at this⟩

theorem centerOf_eq_of_abelian {X : Subgroup Mb} (h : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    centerOf X = X := by
  ext x
  rw [mem_centerOf_iff]
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun t ht => h t ht x hx⟩⟩

end LieSide

section Generic

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {N : Subgroup Mb} {b : ↥N →* G}
  {M : Subgroup G}

theorem map_mem_centerOf_perfectCore (hb : Function.Injective b) (hrange : b.range = M) {x : Mb}
    (hxN : x ∈ N) (hxZ : x ∈ centerOf (perfectCore N)) : b ⟨x, hxN⟩ ∈ centerOf (perfectCore M) := by
  rw [← hrange, ← subImg_self b, subImg_perfectCore hb le_rfl,
    subImg_centerOf hb (perfectCore_le N)]
  exact mem_subImg_of_mem b hxN hxZ

theorem orderOf_img (hb : Function.Injective b) {x : Mb} (hxN : x ∈ N) :
    orderOf (b ⟨x, hxN⟩) = orderOf x :=
  (orderOf_injective b hb ⟨x, hxN⟩).trans (Subgroup.orderOf_coe (⟨x, hxN⟩ : ↥N)).symm

theorem mem_of_Z_conj (hb : Function.Injective b) (hrange : b.range = M)
    (hcent : ∀ z ∈ centerOf (perfectCore M), orderOf z = 2 →
      Subgroup.centralizer ({z} : Set G) ≤ M)
    {x y m : Mb} (hxN : x ∈ N) (hyN : y ∈ N) (hmN : m ∈ N) (hxZ : x ∈ centerOf (perfectCore N))
    (hx2 : orderOf x = 2) (hmxy : m * x * m⁻¹ = y) {g : G}
    (hg : g * b ⟨x, hxN⟩ * g⁻¹ = b ⟨y, hyN⟩) : g ∈ M := by
  have hz := map_mem_centerOf_perfectCore hb hrange hxN hxZ
  have hord : orderOf (b ⟨x, hxN⟩) = 2 := (orderOf_img hb hxN).trans hx2
  set c : G := b ⟨m, hmN⟩ with hc
  have hy : b ⟨y, hyN⟩ = c * b ⟨x, hxN⟩ * c⁻¹ := by
    have : (⟨y, hyN⟩ : ↥N) = ⟨m, hmN⟩ * ⟨x, hxN⟩ * ⟨m, hmN⟩⁻¹ := Subtype.ext hmxy.symm
    rw [this, map_mul, map_mul, map_inv]
  have hcM : c ∈ M := hrange ▸ ⟨⟨m, hmN⟩, rfl⟩
  have hmem : c⁻¹ * g ∈ Subgroup.centralizer ({b ⟨x, hxN⟩} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * b ⟨x, hxN⟩ * g⁻¹ = c * b ⟨x, hxN⟩ * c⁻¹ := hg.trans hy
    calc c⁻¹ * g * b ⟨x, hxN⟩ = c⁻¹ * (g * b ⟨x, hxN⟩ * g⁻¹) * g := by group
      _ = c⁻¹ * (c * b ⟨x, hxN⟩ * c⁻¹) * g := by rw [h1]
      _ = b ⟨x, hxN⟩ * (c⁻¹ * g) := by group
  have := hcent _ hz hord hmem
  have e : g = c * (c⁻¹ * g) := by group
  rw [e]
  exact M.mul_mem hcM this

end Generic

section GSide

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {T N1 N2 : Subgroup Mb} {I : Finset Mb}
  {b1 : ↥N1 →* G} {b2 : ↥N2 →* G} {M1 M2 : Subgroup G}

structure SpGSetup (N1 N2 : Subgroup Mb) (b1 : ↥N1 →* G) (b2 : ↥N2 →* G) (M1 M2 : Subgroup G) :
    Prop where
  comp : F431Comp N1 N2 b1 b2
  range1 : b1.range = M1
  range2 : b2.range = M2
  inter : ∀ g : G, g ∈ M1 → g ∈ M2 → ∃ n : Mb, ∃ (h1 : n ∈ N1) (_ : n ∈ N2), b1 ⟨n, h1⟩ = g
  normalizer1 : Subgroup.normalizer (centerOf (pCoreOf 2 M1) : Set G) = M1
  normalizer2 : Subgroup.normalizer (centerOf (pCoreOf 2 M2) : Set G) = M2
  cent1 : ∀ z ∈ centerOf (perfectCore M1), orderOf z = 2 →
    Subgroup.centralizer ({z} : Set G) ≤ M1
  cent2 : ∀ z ∈ centerOf (perfectCore M2), orderOf z = 2 →
    Subgroup.centralizer ({z} : Set G) ≤ M2
  charTwo : ∀ u ∈ centerOf (pCoreOf 2 (M1 ⊓ M2)), orderOf u = 2 →
    CharTwo (Subgroup.centralizer ({u} : Set G))
  odd : ¬ 2 ∣ (M1 ⊓ M2).index

namespace SpGSetup

variable (S : SpGSetup N1 N2 b1 b2 M1 M2)

include S

theorem inter_eq : M1 ⊓ M2 = subImg b1 (N1 ⊓ N2) := by
  ext g
  constructor
  · rintro ⟨hg1, hg2⟩
    obtain ⟨n, h1, h2, hn⟩ := S.inter g hg1 hg2
    exact mem_subImg.mpr ⟨n, h1, ⟨h1, h2⟩, hn⟩
  · intro hg
    obtain ⟨n, hn1, ⟨-, hn2⟩, rfl⟩ := mem_subImg.mp hg
    refine ⟨?_, ?_⟩
    · rw [← S.range1]
      exact ⟨⟨n, hn1⟩, rfl⟩
    · rw [← S.range2]
      exact ⟨⟨n, hn2⟩, (S.comp.agree n hn1 hn2).symm⟩

theorem centerOf_pCore₁ (L : F431SpLie T N1 N2 I) :
    centerOf (pCoreOf 2 M1) = subImg b1 (pCoreOf 2 N1) := by
  obtain rfl := S.range1
  have hab : ∀ x ∈ pCoreOf 2 N1, ∀ y ∈ pCoreOf 2 N1, x * y = y * x := L.Q_abel 0
  rw [← subImg_self b1, subImg_pCoreOf S.comp.inj₁ le_rfl,
    subImg_centerOf S.comp.inj₁ (LieType.BorelTits.pCoreOf_le 2 N1), centerOf_eq_of_abelian hab]

theorem centerOf_pCore₂ [Finite Mb] (L : F431SpLie T N1 N2 I) :
    centerOf (pCoreOf 2 M2) = subImg b1 (pCoreOf 2 N2) := by
  have hab : ∀ x ∈ pCoreOf 2 N2, ∀ y ∈ pCoreOf 2 N2, x * y = y * x := L.Q_abel 1
  have h2 : centerOf (pCoreOf 2 M2) = subImg b2 (pCoreOf 2 N2) := by
    obtain rfl := S.range2
    rw [← subImg_self b2, subImg_pCoreOf S.comp.inj₂ le_rfl,
      subImg_centerOf S.comp.inj₂ (LieType.BorelTits.pCoreOf_le 2 N2), centerOf_eq_of_abelian hab]
  rw [h2]
  exact (subImg_eq_of_agree S.comp.agree ((spQ_le L 1).trans L.W.T_le₁)
    (LieType.BorelTits.pCoreOf_le 2 N2)).symm

theorem normalizer_Q [Finite Mb] (L : F431SpLie T N1 N2 I) (j : Fin 2) :
    Subgroup.normalizer (subImg b1 (spQ N1 N2 j) : Set G) = ![M1, M2] j := by
  fin_cases j
  · show Subgroup.normalizer (subImg b1 (pCoreOf 2 N1) : Set G) = M1
    rw [← S.centerOf_pCore₁ L]
    exact S.normalizer1
  · show Subgroup.normalizer (subImg b1 (pCoreOf 2 N2) : Set G) = M2
    rw [← S.centerOf_pCore₂ L]
    exact S.normalizer2

theorem sylow (L : F431SpLie T N1 N2 I) : IsSylowTwoOf (subImg b1 T) ⊤ :=
  isSylowTwoOf_image_of_odd_index S.comp S.range1 S.range2 L.W.sylow L.W.T_le₁ L.W.T_le₂ S.odd

theorem shape [Finite Mb] (L : F431SpLie T N1 N2 I) :
    SpShape (subImg b1 T) (fun j => subImg b1 (spQ N1 N2 j)) where
  Q_le j := subImg_mono b1 (spQ_le L j)
  Q_norm j := subImg_le_normalizer b1 (T_le_normalizer_spQ L j)
  Q_abel j := by
    intro x hx y hy
    obtain ⟨x', hx'N, hx'Q, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy'N, hy'Q, rfl⟩ := mem_subImg.mp hy
    exact (commute_iff_of_injective S.comp.inj₁ hy'N hx'N).mpr (L.Q_abel j x' hx'Q y' hy'Q)
  Z_le j := by
    rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁]
    exact subImg_mono b1 (L.Z_le_Q j)
  Z_sq := by
    intro z hz
    rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁] at hz
    obtain ⟨z', hz'N, hz'Z, rfl⟩ := mem_subImg.mp hz
    exact (sq_eq_one_iff_of_injective S.comp.inj₁ hz'N).mpr (L.Z_sq z' hz'Z)
  inv_mem := by
    intro x hx hx2
    obtain ⟨x', hx'N, hx'T, rfl⟩ := mem_subImg.mp hx
    obtain ⟨j, hj⟩ := L.inv_mem x' hx'T ((sq_eq_one_iff_of_injective S.comp.inj₁ hx'N).mp hx2)
    exact ⟨j, mem_subImg_of_mem b1 hx'N hj⟩
  cen j := by
    intro x hx hxZ y hy hcomm
    obtain ⟨x', hx'N, hx'Q, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy'N, hy'T, rfl⟩ := mem_subImg.mp hy
    have hx'Z : x' ∉ centerOf T := fun h => hxZ (by
      rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁]
      exact mem_subImg_of_mem b1 hx'N h)
    have hcomm' : y' * x' = x' * y' :=
      (commute_iff_of_injective S.comp.inj₁ hx'N hy'N).mp hcomm
    exact mem_subImg_of_mem b1 hy'N (L.cen j x' hx'Q hx'Z y' hy'T hcomm')
  ex j := by
    obtain ⟨x, hxQ, hxZ, hx2⟩ := L.ex j
    have hxN : x ∈ N1 := L.W.T_le₁ (spQ_le L j hxQ)
    refine ⟨b1 ⟨x, hxN⟩, mem_subImg_of_mem b1 hxN hxQ, fun h => hxZ ?_,
      (sq_eq_one_iff_of_injective S.comp.inj₁ hxN).mpr hx2⟩
    rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁] at h
    exact (mem_subImg_iff_of_injective S.comp.inj₁ hxN).mp h

theorem normalizer_le [Finite Mb] [Finite G] (L : F431SpLie T N1 N2 I) {n : G}
    (hn : n ∈ Subgroup.normalizer (subImg b1 T : Set G)) : n ∈ M1 ∧ n ∈ M2 := by
  have h0 := (S.shape L).normalizer_le (S.sylow L) hn 0
  have h1 := (S.shape L).normalizer_le (S.sylow L) hn 1
  rw [S.normalizer_Q L 0] at h0
  rw [S.normalizer_Q L 1] at h1
  exact ⟨h0, h1⟩

theorem not_conj [Finite Mb] [Finite G] (L : F431SpLie T N1 N2 I) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  intro i hi j hj hij hconj
  have hiT : i ∈ T := L.W.mem_T i hi
  have hjT : j ∈ T := L.W.mem_T j hj
  have hiN : i ∈ N1 := L.W.T_le₁ hiT
  have hjN : j ∈ N1 := L.W.T_le₁ hjT
  rw [amalgamMap_of_mem₁ b1 b2 hiN, amalgamMap_of_mem₁ b1 b2 hjN] at hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hu : b1 ⟨i, hiN⟩ ∈ centerOf (subImg b1 T) := by
    rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁]
    exact mem_subImg_of_mem b1 hiN (L.I_center i hi)
  have hv : b1 ⟨j, hjN⟩ ∈ centerOf (subImg b1 T) := by
    rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁]
    exact mem_subImg_of_mem b1 hjN (L.I_center j hj)
  obtain ⟨n, hn, hnuv⟩ := exists_normalizer_conj_of_central (S.sylow L) hu hv hg
  obtain ⟨hn1, hn2⟩ := S.normalizer_le L hn
  obtain ⟨n', h1', h2', hn'⟩ := S.inter n hn1 hn2
  have hconj' : n' * i * n'⁻¹ = j := by
    have e : (⟨n' * i * n'⁻¹, N1.mul_mem (N1.mul_mem h1' hiN) (N1.inv_mem h1')⟩ : ↥N1) =
        ⟨j, hjN⟩ := by
      apply S.comp.inj₁
      have : (⟨n' * i * n'⁻¹, N1.mul_mem (N1.mul_mem h1' hiN) (N1.inv_mem h1')⟩ : ↥N1) =
          ⟨n', h1'⟩ * ⟨i, hiN⟩ * ⟨n', h1'⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hn', hnuv]
    exact congrArg Subtype.val e
  obtain ⟨w, ⟨hwI, hw⟩, huniq⟩ := L.W.rep i (L.W.order_two i hi)
  have h1 : j = w := huniq j ⟨hj, isConj_iff.mpr ⟨n'⁻¹, by rw [← hconj']; group⟩⟩
  have h2 : i = w := huniq i ⟨hi, IsConj.refl i⟩
  exact hij (h2.trans h1.symm)

theorem mem_of_normalizes_Z [Finite Mb] [Finite G] (L : F431SpLie T N1 N2 I) (j : Fin 2) {g : G}
    (hZ : ∀ z ∈ centerOf (subImg b1 T), g * z * g⁻¹ ∈ centerOf (subImg b1 T)) :
    g ∈ ![M1, M2] j := by
  obtain ⟨x, hxZ, hx1⟩ := L.Z_ne j
  have hxT : x ∈ centerOf T := L.Z_le j hxZ
  have hxTT : x ∈ T := (mem_centerOf_iff.mp hxT).1
  have hxN1 : x ∈ N1 := L.W.T_le₁ hxTT
  have hxN2 : x ∈ N2 := L.W.T_le₂ hxTT
  have hx2 : orderOf x = 2 := orderOf_eq_prime (L.Z_sq x hxT) hx1
  have hz : b1 ⟨x, hxN1⟩ ∈ centerOf (subImg b1 T) := by
    rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁]
    exact mem_subImg_of_mem b1 hxN1 hxT
  have hgz := hZ _ hz
  rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁] at hgz
  obtain ⟨y, hyN1, hyT, hy⟩ := mem_subImg.mp hgz
  have hyTT : y ∈ T := (mem_centerOf_iff.mp hyT).1
  have hy1 : y ≠ 1 := by
    rintro rfl
    have h1 : g * b1 ⟨x, hxN1⟩ * g⁻¹ = 1 := by
      rw [← hy]
      exact map_one b1
    have h2 : b1 ⟨x, hxN1⟩ = 1 := by
      have := congrArg (fun w => g⁻¹ * w * g) h1
      simpa [mul_assoc] using this
    exact hx1 (congrArg Subtype.val (S.comp.inj₁ (h2.trans (map_one b1).symm)))
  have hy2 : orderOf y = 2 := orderOf_eq_prime (L.Z_sq y hyT) hy1
  have hconj : IsConj x y := by
    have := (L.W.lemma_F435 S.comp (S.not_conj L) hxTT hyTT hx2 hy2).mpr
    refine this ?_
    rw [amalgamMap_of_mem₁ b1 b2 hxN1, amalgamMap_of_mem₁ b1 b2 hyN1]
    exact isConj_iff.mpr ⟨g, hy.symm⟩
  have hyZ : y ∈ spZ N1 N2 j := L.Z_cls j x hxZ y hyT hconj
  obtain ⟨m, hm, hmxy⟩ := L.Z_trans j x hxZ y hyZ hx1 hy1
  fin_cases j
  · exact mem_of_Z_conj S.comp.inj₁ S.range1 S.cent1 hxN1 hyN1 hm hxZ hx2 hmxy hy.symm
  · have hyN2 : y ∈ N2 := L.W.T_le₂ hyTT
    refine mem_of_Z_conj S.comp.inj₂ S.range2 S.cent2 hxN2 hyN2 hm hxZ hx2 hmxy ?_
    rw [← S.comp.agree x hxN1 hxN2, ← S.comp.agree y hyN1 hyN2]
    exact hy.symm

theorem centralizer_c2 [Finite Mb] [Finite G] (L : F431SpLie T N1 N2 I) {i : Mb} (hi : i ∈ I)
    (hC : Subgroup.centralizer ({i} : Set Mb) ≤ N1 ⊓ N2) :
    Subgroup.centralizer ({amalgamMap b1 b2 i} : Set G) ≤ M1 ⊓ M2 := by
  have hiT : i ∈ T := L.W.mem_T i hi
  have hiN : i ∈ N1 := L.W.T_le₁ hiT
  have hiN2 : i ∈ N2 := L.W.T_le₂ hiT
  rw [amalgamMap_of_mem₁ b1 b2 hiN]
  set u : G := b1 ⟨i, hiN⟩ with hu
  have huZ : u ∈ centerOf (subImg b1 T) := by
    rw [subImg_centerOf S.comp.inj₁ L.W.T_le₁]
    exact mem_subImg_of_mem b1 hiN (L.I_center i hi)
  have hu2 : orderOf u = 2 := (orderOf_img S.comp.inj₁ hiN).trans (L.W.order_two i hi)
  have hpc : pCoreOf 2 (M1 ⊓ M2) = subImg b1 T := by
    rw [S.inter_eq, subImg_pCoreOf S.comp.inj₁ inf_le_left, L.O2N12]
  have hchar := S.charTwo u (by rw [hpc]; exact huZ) hu2
  intro g hg
  rcases (S.shape L).centralizer_cases (S.sylow L) huZ hchar with ⟨j, hj⟩ | hZ
  · have hgj : g ∈ ![M1, M2] j := by
      rw [← S.normalizer_Q L j]
      exact hj hg
    have hgu : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    fin_cases j
    · obtain ⟨⟨n, hnN⟩, rfl⟩ : g ∈ b1.range := S.range1 ▸ hgj
      have hn : n ∈ Subgroup.centralizer ({i} : Set Mb) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commute_iff_of_injective S.comp.inj₁ hiN hnN).mp hgu
      have hn12 := hC hn
      refine ⟨S.range1 ▸ ⟨⟨n, hnN⟩, rfl⟩, ?_⟩
      rw [← S.range2]
      exact ⟨⟨n, hn12.2⟩, (S.comp.agree n hnN hn12.2).symm⟩
    · obtain ⟨⟨n, hnN⟩, rfl⟩ : g ∈ b2.range := S.range2 ▸ hgj
      have hu' : u = b2 ⟨i, hiN2⟩ := S.comp.agree i hiN hiN2
      have hn : n ∈ Subgroup.centralizer ({i} : Set Mb) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [hu'] at hgu
        exact (commute_iff_of_injective S.comp.inj₂ hiN2 hnN).mp hgu
      have hn12 := hC hn
      refine ⟨?_, S.range2 ▸ ⟨⟨n, hnN⟩, rfl⟩⟩
      rw [← S.range1]
      exact ⟨⟨n, hn12.1⟩, S.comp.agree n hn12.1 hnN⟩
  · exact ⟨S.mem_of_normalizes_Z L 0 (hZ g hg), S.mem_of_normalizes_Z L 1 (hZ g hg)⟩

theorem core [Finite Mb] [Finite G] (L : F431SpLie T N1 N2 I) :
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j)) ∧
    (∀ i ∈ I,
      (Subgroup.centralizer ({i} : Set Mb) ≤ N1 ∧
        Subgroup.centralizer ({amalgamMap b1 b2 i} : Set G) ≤ M1) ∨
      (Subgroup.centralizer ({i} : Set Mb) ≤ N2 ∧
        Subgroup.centralizer ({amalgamMap b1 b2 i} : Set G) ≤ M2)) := by
  refine ⟨S.not_conj L, fun i hi => ?_⟩
  have hiT : i ∈ T := L.W.mem_T i hi
  have hiN1 : i ∈ N1 := L.W.T_le₁ hiT
  have hiN2 : i ∈ N2 := L.W.T_le₂ hiT
  rcases L.I_type i hi with ⟨hZ, hC⟩ | ⟨hZ, hC⟩ | hC
  · left
    refine ⟨hC, ?_⟩
    rw [amalgamMap_of_mem₁ b1 b2 hiN1]
    exact S.cent1 _ (map_mem_centerOf_perfectCore S.comp.inj₁ S.range1 hiN1 hZ)
      ((orderOf_img S.comp.inj₁ hiN1).trans (L.W.order_two i hi))
  · right
    refine ⟨hC, ?_⟩
    rw [amalgamMap_of_mem₂ b1 b2 S.comp.agree hiN2]
    exact S.cent2 _ (map_mem_centerOf_perfectCore S.comp.inj₂ S.range2 hiN2 hZ)
      ((orderOf_img S.comp.inj₂ hiN2).trans (L.W.order_two i hi))
  · left
    exact ⟨hC.trans inf_le_left, (S.centralizer_c2 L hi hC).trans inf_le_left⟩

end SpGSetup

end GSide

theorem LieExt.inter_mem {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}
    (E : LieExt D M1 M2) :
    ∀ g : G, g ∈ M1 → g ∈ M2 →
      ∃ n : ↥E.K, ∃ (h1 : n ∈ E.Mb1) (_ : n ∈ E.Mb2), E.b1 ⟨n, h1⟩ = g := by
  intro g hg1 hg2
  set w' : ↥(M1 ⊓ M2) := ⟨g, hg1, hg2⟩ with hw'
  have hx1 : ((E.phi12 w' : ↥(E.N1 ⊓ E.N2)) : MulAut D) ∈ E.N1 := (E.phi12 w').2.1
  have hx2 : ((E.phi12 w' : ↥(E.N1 ⊓ E.N2)) : MulAut D) ∈ E.N2 := (E.phi12 w').2.2
  have hxK : ((E.phi12 w' : ↥(E.N1 ⊓ E.N2)) : MulAut D) ∈ E.K := E.N1_le_K hx1
  refine ⟨⟨_, hxK⟩, Subgroup.mem_subgroupOf.mpr hx1, Subgroup.mem_subgroupOf.mpr hx2, ?_⟩
  rw [E.b1_apply]
  have e1 : E.phi1.symm ⟨_, hx1⟩ = (⟨g, hg1⟩ : ↥M1) := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (E.phi1_phi12 w').symm
  rw [e1]

theorem f431SpLocal_of_lie {f : ℕ} (hLie : F431SpLieProp f) : F431SpLocal f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E hodd
  have hKne : Nat.card ↥E.K ≠ 0 := by
    intro h
    rw [h, Nat.zero_div] at hodd
    exact absurd hodd (by decide)
  have : Finite ↥E.K := Nat.finite_of_card_ne_zero hKne
  obtain ⟨T, I, L⟩ := hLie D hD E.toLieAmalgamExt hodd
  have ha := hyps.2.1 (Or.inl rfl)
  have hb := hyps.2.2.2.1 (by simp)
  have hd := hyps.2.2.2.2 rfl
  have S : SpGSetup E.Mb1 E.Mb2 E.b1 E.b2 M1 M2 :=
    ⟨E.comp, E.range_b1, E.range_b2, E.inter_mem, ha.1, ha.2, hb.1, hb.2, hd.1, hd.2⟩
  obtain ⟨hnf, hc⟩ := S.core L
  exact ⟨T, I, L.W, hnf, hc⟩

end CFSG.Quasithin.H13.F431
