module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110Gen
public import CFSG.Quasithin.Vol2.Ch11SecBL2UPSU
public import CFSG.Quasithin.EmptyFaithful.S146zXGOrder
public import CFSG.Quasithin.H13.A5S136ModL34
public import CFSG.Quasithin.Background.S1567Y
public import CFSG.Quasithin.EmptyFaithful.S153EB6E
public import CFSG.Quasithin.Vol2.Ch9Prop927

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G]

namespace L34

theorem mem_normalizer_of_forall {A : Subgroup G} {c : G} (h : ∀ v ∈ A, c * v * c⁻¹ ∈ A) :
    c ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj c).toMonoidHom ≤ A := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have hcard : Nat.card ↥(A.map (MulAut.conj c).toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have heq : A.map (MulAut.conj c).toMonoidHom = A := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : x = y := by
    have h1 : c * y * c⁻¹ = c * x * c⁻¹ := hyx
    exact (mul_left_cancel (mul_right_cancel h1)).symm
  rw [this]
  exact hy

theorem eq_of_mem_cComp_sup {H K K' T : Subgroup G} (hKc : K ∈ cComp H) (hK'c : K' ∈ cComp H)
    (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hT : IsPGroup 2 T) :
    K' = K := by
  have hperf : Group.IsPerfect ↥K' := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK'c)
  have h1 : K' ≤ oTwoUpper H := perfect_le_oTwoUpper (le_of_mem_cComp hK'c) hperf
  rw [hHK] at h1
  have hle : K' ≤ K := h1.trans (S1567.oTwoUpper_sup_le hTK hT)
  by_contra hne
  exact not_subnormal_of_mem_cComp hKc (lt_of_le_of_ne hle hne) (ne_bot_of_mem_cComp hK'c)
    (perfect_of_mem_cComp hK'c) (subnormal_of_mem_cComp hK'c)

theorem not_isBenderOf_of_psl34 {X : Type} [Group X] {n : ℕ} (hB : E2.IsBenderOf n X)
    (hL : IsPSL 3 2 2 X) : False := by
  have hc := Ch1Four.card_of_isPSL_three_four hL
  obtain ⟨hn, h | h | h⟩ := hB
  · have h1 := S146zX.card_isPSL_two_even h
    rw [hc, show (2 ^ n) ^ 2 = 4 ^ n by rw [← pow_mul, mul_comm, pow_mul]; norm_num] at h1
    exact A5.psl22_ne_20160 n h1.symm
  · exact S146zX.not_three_dvd_card_isSz h (by rw [hc]; norm_num)
  · have h1 := Vol2.Ch11.SecB.card_isPSU3 h
    have h2 := Vol2.Ch11.SecB.lt_ordTwistedA_two hn
    omega

end L34

variable {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem isDiagramNontrivial_star_of_l34 (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1)
    {H K : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H)
    (hHK : H = K ⊔ T) (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K)) :
    E2.IsDiagramNontrivial (E2.star (H ⊓ fsuM T L) H T) (E2.star (H ⊓ fsuM T L) H K)
      (E2.star (H ⊓ fsuM T L) H (T ⊓ K)) := by
  obtain ⟨hmin, hSQ, hns, hTXs⟩ := S.minParabolic_of_isHStar h331 hH hn1
  obtain ⟨⟨K', hK'c, hHK', -, hcases⟩, -⟩ := hE22.exists_cases hmin hSQ hns
  have hK' : K' = K := L34.eq_of_mem_cComp_sup hKc hK'c hHK hTK hTXs.2.1
  rw [hK'] at hcases
  dsimp only [E2.E22CasesC] at hcases
  rcases hcases with ⟨-, t, ht, hne, -, -⟩ | ⟨-, -, h2⟩
  · exfalso
    apply hne
    ext x
    rw [mem_cjSub]
    have h1 := Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (K : Set G)).inv_mem (hTK ht)) x
    rw [inv_inv] at h1
    exact h1.symm
  · rcases h2 with ⟨m, hBen, -, -, -⟩ | ⟨m, -, -, hD, -⟩ | ⟨_, _, _, _, _, _, _, _, _, hnH1⟩ |
        ⟨_, _, _, _, _, hnH1⟩
    · exact (L34.not_isBenderOf_of_psl34 hBen hKL).elim
    · exact hD
    · exact absurd hn1 (by rw [hnH1]; exact lt_irrefl 1)
    · exact absurd hn1 (by rw [hnH1]; exact lt_irrefl 1)

theorem isDiagramNontrivial_of_l34 (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1)
    {H K : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H)
    (hHK : H = K ⊔ T) (hKc : K ∈ cComp H) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hJ : IsPGroup 2 (kerIn (H ⊓ fsuM T L) H))
    (hKL : IsPSL 3 2 2 ↥(E2.star (H ⊓ fsuM T L) H K)) :
    E2.IsDiagramNontrivial T K (T ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := S.isDiagramNontrivial_star_of_l34 hE22 h331 hH hn1 hHK hKc hTK hKL
  set X := H ⊓ fsuM T L with hX
  set π := starPi X H with hπ
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hH.1.1
  have hTHs : IsSylowTwoOf T H :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hTKs : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTHs hKH hHKn
  have hJK : ∀ j ∈ K, j ∈ kerIn X H → j ∈ T ⊓ K := by
    intro j hjK hjJ
    have hNn : ((K ⊓ kerIn X H).subgroupOf K).Normal := by
      refine ⟨fun a ha k => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      refine ⟨K.mul_mem (K.mul_mem k.2 ha.1) (K.inv_mem k.2), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn X H (hKH k.2)) _).mp ha.2
    have hle := A4.le_of_normal_of_isSylowTwoOf hTKs inf_le_left hNn (hJ.to_le inf_le_right)
    exact hle ⟨hjK, hjJ⟩
  have hpre : ∀ Y : Subgroup G, Y ≤ K → (∀ j ∈ K, j ∈ kerIn X H → j ∈ Y) →
      ∀ k ∈ K, ∀ (hkH : k ∈ H), π ⟨k, hkH⟩ ∈ E2.star X H Y → k ∈ Y := by
    intro Y hYK hJY k hk hkH hkY
    obtain ⟨y, hy, hyk⟩ := mem_star510_iff.mp hkY
    have h1 := starPi_eq_iff.mp hyk
    have h3 := hJY _ (K.mul_mem (K.inv_mem (hYK hy)) hk) h1
    have := Y.mul_mem hy h3
    simpa using this
  have hTKpre := hpre (T ⊓ K) inf_le_right hJK
  have hNpre : ∀ m ∈ K, ∀ (hmH : m ∈ H), π ⟨m, hmH⟩ ∈ Subgroup.normalizer
      ((E2.star X H (T ⊓ K) : Subgroup (E2.StarQuot X H)) : Set (E2.StarQuot X H)) →
      m ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    intro m hm hmH hmN
    refine L34.mem_normalizer_of_forall fun x hx => ?_
    have hxH : x ∈ H := hTH hx.1
    have hmx : m * x * m⁻¹ ∈ K := K.mul_mem (K.mul_mem hm hx.2) (K.inv_mem hm)
    refine hTKpre _ hmx (H.mul_mem (H.mul_mem hmH hxH) (H.inv_mem hmH)) ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hmN (π ⟨x, hxH⟩)).mp (starPi_mem_star hx)
    have h2 : π ⟨m * x * m⁻¹, H.mul_mem (H.mul_mem hmH hxH) (H.inv_mem hmH)⟩ =
        π ⟨m, hmH⟩ * π ⟨x, hxH⟩ * (π ⟨m, hmH⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2]
    exact h1
  have hsylKs : IsSylowTwoOf (E2.star X H (T ⊓ K)) (E2.star X H K) := by
    have h := S153EB6.isSylowTwoOf_map_range ((starPi X H).comp (Subgroup.inclusion hKH)) hTKs
    rwa [map_comp_inclusion_eq_star hKH inf_le_right, range_comp_inclusion_eq_star hKH] at h
  intro P hP hBP hTP
  have hPK : P ≤ K := hP.1.1
  have hJP : ∀ j ∈ K, j ∈ kerIn X H → j ∈ P := fun j hjK hjJ =>
    hBP ⟨hjK, Subgroup.le_normalizer (hJK j hjK hjJ)⟩
  have hPpre := hpre P hPK hJP
  have hBs : E2.star X H K ⊓ Subgroup.normalizer ((E2.star X H (T ⊓ K) : Subgroup _) :
      Set (E2.StarQuot X H)) ≤ E2.star X H P := by
    rintro y ⟨hyK, hyN⟩
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hyK
    exact starPi_mem_star (hBP ⟨hx, hNpre x hx x.2 hyN⟩)
  have hPs_le : E2.star X H P ≤ E2.star X H K := Subgroup.map_mono fun x hx => hPK hx
  refine hD (E2.star X H P) ⟨⟨hPs_le, E2.star X H (T ⊓ K), hsylKs, hBs⟩, ?_, ?_⟩ hBs ?_
  ·
    intro heq
    apply hP.2.1
    refine le_antisymm hPK fun k hk => hPpre k hk (hKH hk) ?_
    rw [heq]
    exact starPi_mem_star hk
  ·
    intro Q' hQ' hQ'K hPQ'
    set P₁ := K ⊓ (Q'.comap π).map H.subtype with hP₁
    have hPP₁ : P ≤ P₁ := fun p hp =>
      ⟨hPK hp, ⟨⟨p, hKH (hPK hp)⟩, hPQ' (starPi_mem_star hp), rfl⟩⟩
    have hP₁par : IsParabolic2 K P₁ := ⟨inf_le_left, T ⊓ K, hTKs, hBP.trans hPP₁⟩
    have hP₁ne : P₁ ≠ K := by
      intro h
      apply hQ'K
      refine le_antisymm hQ'.1 fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp hy
      have hx' : (x : G) ∈ P₁ := by rw [h]; exact hx
      obtain ⟨x', hx'Q, hxx'⟩ := hx'.2
      rw [show x = x' from Subtype.ext hxx'.symm]
      exact hx'Q
    have hP₁eq := hP.2.2 P₁ hP₁par hP₁ne hPP₁
    refine le_antisymm (fun y hy => ?_) hPQ'
    obtain ⟨x, hx, rfl⟩ := mem_star510_iff.mp (hQ'.1 hy)
    have hxP₁ : (x : G) ∈ P₁ := ⟨hx, ⟨x, hy, rfl⟩⟩
    rw [hP₁eq] at hxP₁
    exact starPi_mem_star hxP₁
  ·
    intro y hy
    obtain ⟨t, ht, rfl⟩ := mem_star510_iff.mp hy
    exact starPi_mem_normalizer (hTP ht)

end Setup

end CFSG.Quasithin.H13.Ch9
