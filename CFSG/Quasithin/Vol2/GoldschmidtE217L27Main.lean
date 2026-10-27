module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Red
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3TwoC
public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Cent
public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Quot
public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Orc
public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Loc
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect4
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M E217R3

namespace E217L27

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_starMap_mem {H T M : Subgroup G} (hJT : kerIn M H ≤ T) (g : ↥H)
    (hg : E2P.starMap M H g ∈ E2.star M H T) : (g : G) ∈ T := by
  obtain ⟨t, ht, hgt⟩ := hg
  have h0 : t⁻¹ * g ∈ (E2P.starMap M H).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : E2P.starMap M H t = E2P.starMap M H g := hgt
    rw [this, inv_mul_cancel]
  rw [E2P.ker_starMap] at h0
  have h1 : ((t⁻¹ * g : ↥H) : G) ∈ kerIn M H := Subgroup.mem_subgroupOf.1 h0
  have h2 : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
  have h3 : (t : G) * ((t⁻¹ * g : ↥H) : G) ∈ T := T.mul_mem h2 (hJT h1)
  simpa using h3

omit [Finite G] in
theorem exists_mem_not_mem {B Z : Subgroup G} (hZB : Z ≤ B) (hB : Nat.card B = 8)
    (hZ : Nat.card Z = 2) : ∃ b ∈ B, b ∉ Z := by
  have hlt : Z < B := lt_of_le_of_ne hZB fun h => by
    have : Nat.card Z = Nat.card B := by rw [h]
    omega
  obtain ⟨b, hb, hbZ⟩ := IsConcreteLE.exists_of_lt hlt
  exact ⟨b, hb, hbZ⟩

theorem exists_z {H T M V K : Subgroup G} (h : Hyp2 H T M V) (hL : L27c ↥(E2.star M H K)) {x : G}
    (hxH : x ∈ H) (hxV : x ∈ V) (hxQ : x ∉ pCoreOf 2 H)
    (hv2 : E2P.starMap M H ⟨x, hxH⟩ * E2P.starMap M H ⟨x, hxH⟩ = 1)
    (hv1 : E2P.starMap M H ⟨x, hxH⟩ ≠ 1) (hvK : E2P.starMap M H ⟨x, hxH⟩ ∈ E2.star M H K) :
    ∃ (z : G) (d : DihedralPair H T V (V ⊓ pCoreOf 2 H) x z),
      E2P.starMap M H ⟨z, d.zH⟩ ∈ E2.star M H K ∧ E2P.starMap M H ⟨z, d.zH⟩ ^ 3 = 1 ∧
        E2P.starMap M H ⟨z, d.zH⟩ ≠ 1 ∧
        E2P.starMap M H ⟨x, hxH⟩ * E2P.starMap M H ⟨z, d.zH⟩ * (E2P.starMap M H ⟨x, hxH⟩)⁻¹ =
          (E2P.starMap M H ⟨z, d.zH⟩)⁻¹ := by
  set π := E2P.starMap M H with hπ
  set v := π ⟨x, hxH⟩ with hv
  have hx2 : x * x = 1 := by simpa [pow_two] using h.hyp.elem.2 x hxV
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  obtain ⟨a, ha3, ha1, hva⟩ := hL.l27.inv3 ⟨v, hvK⟩ (Subtype.ext hv2)
    (fun h1 => hv1 (congrArg Subtype.val h1))
  obtain ⟨κ, hκK, hκ⟩ := a.2
  have hgH : (κ : G) ∈ H := κ.2
  set y : G := x * ((κ : G) * x * (κ : G)⁻¹) with hy
  have hyH : y ∈ H := H.mul_mem hxH (H.mul_mem (H.mul_mem hgH hxH) (H.inv_mem hgH))
  have hyH' : (⟨y, hyH⟩ : ↥H) = ⟨x, hxH⟩ * (κ * ⟨x, hxH⟩ * κ⁻¹) := rfl
  have hw2 : ((κ : G) * x * (κ : G)⁻¹) * ((κ : G) * x * (κ : G)⁻¹) = 1 := by
    calc ((κ : G) * x * (κ : G)⁻¹) * ((κ : G) * x * (κ : G)⁻¹) = κ * (x * x) * (κ : G)⁻¹ := by
          group
      _ = 1 := by rw [hx2]; group
  have hwi : ((κ : G) * x * (κ : G)⁻¹)⁻¹ = (κ : G) * x * (κ : G)⁻¹ :=
    inv_eq_of_mul_eq_one_right hw2
  have hxy : x * y * x⁻¹ = y⁻¹ := by
    have e1 : x * y * x⁻¹ = (κ : G) * x * (κ : G)⁻¹ * x := by
      rw [hy, hxi]
      calc x * (x * ((κ : G) * x * (κ : G)⁻¹)) * x
          = (x * x) * ((κ : G) * x * (κ : G)⁻¹) * x := by group
        _ = (κ : G) * x * (κ : G)⁻¹ * x := by rw [hx2, one_mul]
    have e2 : y⁻¹ = (κ : G) * x * (κ : G)⁻¹ * x := by
      rw [hy, mul_inv_rev, hwi, hxi]
    rw [e1, e2]
  have hπy : π ⟨y, hyH⟩ = (a : E2.StarQuot M H) := by
    have hva' : v * (a : E2.StarQuot M H) * v⁻¹ = (a : E2.StarQuot M H)⁻¹ :=
      congrArg Subtype.val hva
    have ha3' : (a : E2.StarQuot M H) ^ 3 = 1 := congrArg Subtype.val ha3
    have hv2' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
    have haa : (a : E2.StarQuot M H) * a * a = 1 := by
      calc (a : E2.StarQuot M H) * a * a = (a : E2.StarQuot M H) ^ 3 := by
            rw [pow_succ, pow_two]
        _ = 1 := ha3'
    rw [hyH', map_mul, map_mul, map_mul, map_inv, hκ]
    calc v * (↑a * v * (↑a)⁻¹) = (v * ↑a * v⁻¹) * (v * v) * (↑a)⁻¹ := by group
      _ = (↑a)⁻¹ * (↑a)⁻¹ := by rw [hva', hv2, mul_one]
      _ = ((↑a : E2.StarQuot M H) * ↑a)⁻¹ := by group
      _ = (↑a : E2.StarQuot M H)⁻¹⁻¹ := by rw [eq_inv_of_mul_eq_one_left haa]
      _ = ↑a := inv_inv _
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hzord : orderOf (y ^ 2 ^ s) = t := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨t, hst⟩, hst,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hzH : y ^ 2 ^ s ∈ H := H.pow_mem hyH _
  have hπz : π ⟨y ^ 2 ^ s, hzH⟩ = (a : E2.StarQuot M H) ^ 2 ^ s := by
    have : (⟨y ^ 2 ^ s, hzH⟩ : ↥H) = ⟨y, hyH⟩ ^ 2 ^ s := rfl
    rw [this, map_pow, hπy]
  have hzX1 : π ⟨y ^ 2 ^ s, hzH⟩ ≠ 1 := by
    rw [hπz]
    intro h1
    have h2 : a ^ 2 ^ s = 1 := Subtype.ext h1
    have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have h3 : 3 ∣ 2 ^ s := hord ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hz1 : y ^ 2 ^ s ≠ 1 := fun h1 => hzX1 (by
    have : (⟨y ^ 2 ^ s, hzH⟩ : ↥H) = 1 := Subtype.ext h1
    rw [this, map_one])
  have hxz : x * y ^ 2 ^ s * x⁻¹ = (y ^ 2 ^ s)⁻¹ :=
    conj_eq_inv_of_mem_zpowers hxy (Subgroup.npow_mem_zpowers y _)
  have hzodd : Odd (orderOf (y ^ 2 ^ s)) := by rw [hzord]; exact ht
  have d := dihedralPair_of h hxV hxQ hzH hzodd hz1 hxz
  have hz3 : (y ^ 2 ^ s) ^ 3 = 1 := by
    rw [← (pair_counts h d).1]
    exact pow_orderOf_eq_one _
  refine ⟨y ^ 2 ^ s, d, ?_, ?_, hzX1, ?_⟩
  · rw [hπz]
    exact (E2.star M H K).pow_mem a.2 _
  · rw [← map_pow]
    have : (⟨y ^ 2 ^ s, hzH⟩ : ↥H) ^ 3 = 1 := Subtype.ext hz3
    rw [this, map_one]
  · have h1 : (⟨x, hxH⟩ * ⟨y ^ 2 ^ s, hzH⟩ * ⟨x, hxH⟩⁻¹ : ↥H) = ⟨y ^ 2 ^ s, hzH⟩⁻¹ :=
      Subtype.ext hxz
    have h2 := congrArg π h1
    rw [map_mul, map_mul, map_inv, map_inv] at h2
    exact h2

omit [Finite G] in
theorem setting_of_index_two {X : Type*} [Group X] {K : Subgroup X} (hn : K.Normal)
    (hL : L27c ↥K) (hidx : K.index = 2) : Setting X K := by
  refine ⟨hn, hL, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
    have key : ∀ b : X, b ∉ K → b * a ∈ K := fun b hb => by
      rcases ha b with h | h
      · exact h.1
      · exact absurd h.1 hb
    have h1 : (x * a)⁻¹ * (y * a) ∈ K := K.mul_mem (K.inv_mem (key x hx)) (key y hy)
    have h2 := hn.conj_mem _ h1 a
    have e : a * ((x * a)⁻¹ * (y * a)) * a⁻¹ = x⁻¹ * y := by group
    rwa [e] at h2
  · by_contra hcon
    push Not at hcon
    have : K = ⊤ := eq_top_iff.2 fun n _ => hcon n
    rw [← Subgroup.index_eq_one] at this
    omega

theorem r3Pkg2c7_holds :
    R3Pkg2c7 := by
  intro G _ _ H T M V K hS hlt hC2 hpsl hMK haut
  have h := hS.toHyp2
  have hmp := h.hyp.minParabolic
  have hKc := hS.mem_cComp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hMH : M ≤ H := hmp.maximal.1.le
  have hJ : kerIn M H = pCoreOf 2 H := kerIn_eq_pCoreOf_of_L27 hS hC2 hpsl
  have hJT : kerIn M H ≤ T := hJ ▸ B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
  have hX := asHyp_star_of_psl2 hmp hKc hS.eq_sup hC2 (p := 7) (e := 1) (by norm_num) (Or.inl rfl)
    hpsl
  obtain ⟨F, hFf, hFfin, hF7, ⟨θ⟩⟩ := exists_mulEquiv_psl_seven hpsl
  have hF7' : Nat.card F = 7 := by rw [Nat.card_eq_fintype_card, hF7]
  have hL : L27c ↥(E2.star M H K) := L27c.of_mulEquiv θ (l27c_psl hF7)
  have hK168 : Nat.card ↥(E2.star M H K) = 168 := hL.card
  have hA : Nat.card (MulAut ↥(E2.star M H K)) = 336 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have h168 : Nat.card (CFSG.GorensteinWalter.PSL2 F) = 168 := by
      rw [← Nat.card_congr θ.toEquiv]
      exact hK168
    rw [Nat.card_congr (MulAut.congr θ).toEquiv,
      CFSG.QuasithinUnique.Out21.card_aut (le_refl 7) hF7', h168]
  have hidx := index_eq_two hX hK168 hA haut
  have hD := card_inf_eq_eight hX hK168 hidx haut
  have hS' := setting_of_index_two hX.normal hL hidx
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    E2P.star_inf_T hmp.isSylow hKc.2.2.1 hKH
  have hMK' : E2.star M H M ⊓ E2.star M H K = E2.star M H K ⊓
      Subgroup.centralizer (E2P.zOf (E2.star M H T ⊓ E2.star M H K) :
        Set (E2.StarQuot M H)) := by
    rw [← E2P.star_inf_M, hMK, ← hTK]
    rfl
  have hMT' : E2.star M H M = E2.star M H T := eq_of_inf_eq hX hL hD hMK'
  have hMT : M = T := by
    refine le_antisymm (fun m hm => ?_) hmp.le
    have hmH : m ∈ H := hMH hm
    have : E2P.starMap M H ⟨m, hmH⟩ ∈ E2.star M H M :=
      ⟨⟨m, hmH⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    rw [hMT'] at this
    exact mem_of_starMap_mem hJT ⟨m, hmH⟩ this
  have hTmax : IsMaxSubgroupIn H T := by
    have hu : maxOver H T = {M} := hmp.uniqueMax
    have hmem : M ∈ maxOver H T := by
      rw [hu]
      exact Set.mem_singleton M
    exact hMT ▸ hmem.1
  obtain ⟨x, hxH, hxV, hxQ, hv2, hv1, -, hvM, -⟩ := exists_vbar_aux h
  have hvT' : ∀ t ∈ E2.star M H T, t * E2P.starMap M H ⟨x, hxH⟩ =
      E2P.starMap M H ⟨x, hxH⟩ * t := fun t ht => hvM t (hMT' ▸ ht)
  have hOdd : OddOracle (E2.star M H K) :=
    oddOracle_of_psl_seven hX.normal hX.cent hF7' θ
  have hvK := mem_of_oddOracle hS' hOdd hD hv2 hvT'
  have hC := centralizer_eq_of_eq hX hMT' hv1 hvT'
  obtain ⟨z, d, hzK, hz3, hz1, hvz⟩ := exists_z h hL hxH hxV hxQ hv2 hv1 hvK
  obtain ⟨-, hZ2, -⟩ := pair_counts h d
  have hB8 : Nat.card ↥(V ⊓ pCoreOf 2 H) = 8 := by
    have := d.cardV
    rw [h.V16] at this
    omega
  obtain ⟨b, hb, hbZ⟩ := exists_mem_not_mem d.ZU hB8 hZ2
  obtain ⟨Γ, _, ρ, f, hBF, hf1⟩ := exists_bfun h hTmax hlt d hb hbZ
  refine hf1 (BFun.one_eq_one hBF hS' hOdd (E2P.starMap M H) (E2P.starMap_surjective M H) hvK hv2
    hv1 hzK hz3 hz1 hvz rfl rfl ?_)
  intro g hg
  have hgc : E2P.starMap M H g ∈ Subgroup.centralizer ({E2P.starMap M H ⟨x, hxH⟩} :
      Set (E2.StarQuot M H)) := Subgroup.mem_centralizer_singleton_iff.2 hg
  rw [hC] at hgc
  exact Subgroup.mem_subgroupOf.2 (mem_of_starMap_mem hJT g hgc)

end E217L27

end CFSG.Quasithin
