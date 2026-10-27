module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 E217R3

namespace E217L27

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem dihedralPair_of (h : Hyp2 H T M V) {x z : G} (hxV : x ∈ V)
    (hxQ : x ∉ pCoreOf 2 H) (hzH : z ∈ H) (hzodd : Odd (orderOf z)) (hz1 : z ≠ 1)
    (hxz : x * z * x⁻¹ = z⁻¹) : DihedralPair H T V (V ⊓ pCoreOf 2 H) x z := by
  have hmin := h.hyp.minParabolic
  have hzN : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hzH
  refine ⟨hmin.isSylow.2.1, hmin.isSylow.1, B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow,
    h.charTwo, h.hyp.le_T, h.hyp.normal_T, h.hyp.elem, inf_le_left, le_rfl, hxV,
    fun hx => hxQ hx.2, forall_mem_or_mul_mem_of_relIndex_eq_two h.hyp.elem h.two hxV hxQ, hzH,
    hzodd, hz1, hxz, fun u hu => ?_⟩
  exact (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.mp hzN u).mp hu.2)
    ((pCoreOf 2 H).inv_mem hu.2)

theorem pair_counts (h : Hyp2 H T M V) {x z : G}
    (d : DihedralPair H T V (V ⊓ pCoreOf 2 H) x z) :
    orderOf z = 3 ∧ Nat.card (dpZ V z) = 2 ∧
      V ⊓ Subgroup.centralizer (dpA H V (V ⊓ pCoreOf 2 H) z : Set G) = dpZ V z := by
  obtain ⟨-, hZ2, hCA⟩ := d.counts h.V16 (d.cube_le_sq h.q32)
  exact ⟨d.orderOf_eq_three_of_odd h.V16 h.q32, hZ2, hCA⟩

theorem inf_centralizer_dpP {U : Subgroup G} {x z : G} (d : DihedralPair H T V U x z)
    (hCA : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) :
    dpP H V U z ⊓ Subgroup.centralizer (V : Set G) = U := by
  have hU := d.U_inf_centralizer hCA
  have hA := d.A_inf_centralizer_U hU
  apply le_antisymm
  · rintro p ⟨hp, hpC⟩
    obtain ⟨u, hu, a, ha, rfl⟩ := d.mem_P hp
    have huC : u ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun v hv => B2F.isElemAbelian_comm d.elem hv (d.UV hu)
    have haC : a ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 := Subgroup.mem_centralizer_iff.1 hpC w (d.UV hw)
      have h2 := Subgroup.mem_centralizer_iff.1 huC w (d.UV hw)
      refine mul_left_cancel (a := u) ?_
      calc u * (w * a) = (u * w) * a := by group
        _ = (w * u) * a := by rw [← h2]
        _ = w * (u * a) := by group
        _ = (u * a) * w := h1
        _ = u * (a * w) := by group
    have haZ : a ∈ dpZ V z := hA ▸ ⟨ha, haC⟩
    exact U.mul_mem hu (d.ZU haZ)
  · intro u hu
    exact ⟨Subgroup.mem_sup_left hu,
      Subgroup.mem_centralizer_iff.2 fun v hv => B2F.isElemAbelian_comm d.elem hv (d.UV hu)⟩

omit [Finite G] in
theorem le_normalizer_centralizer {T V : Subgroup G} (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ t ∈ T, ∀ c ∈ T ⊓ Subgroup.centralizer (V : Set G),
      t * c * t⁻¹ ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    intro t ht c hc
    refine ⟨T.mul_mem (T.mul_mem ht hc.1) (T.inv_mem ht),
      Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
    have hv' : t⁻¹ * v * t ∈ V := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem ht)) v).mp hv
    have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hv'
    calc v * (t * c * t⁻¹) = t * ((t⁻¹ * v * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * v * t)) * t⁻¹ := by rw [h1]
      _ = (t * c * t⁻¹) * v := by group
  intro t ht
  exact B6.mem_normalizer_of_forall_mem (key t ht) (fun c hc => by
    simpa using key t⁻¹ (T.inv_mem ht) c hc)

theorem relIndex_ne_zero_of_finite (A B : Subgroup G) : A.relIndex B ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem sup_eq_of_relIndex_lt {P : Subgroup G} (hPT : P ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hP : (T ⊓ Subgroup.centralizer (V : Set G)).relIndex P = 4)
    (hlt : (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8) :
    T ⊓ Subgroup.centralizer (V : Set G) ⊔ P = T := by
  set C := T ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCP : P ≤ Subgroup.normalizer (C : Set G) := hPT.trans (le_normalizer_centralizer hTV)
  have h1 : C.relIndex (P ⊔ C) = C.relIndex P := relIndex_sup_eq_of_le_normalizer hCP
  have hle1 : C ≤ C ⊔ P := le_sup_left
  have hle2 : C ⊔ P ≤ T := sup_le inf_le_left hPT
  have h2 := Subgroup.relIndex_mul_relIndex C (C ⊔ P) T hle1 hle2
  have h4 : C.relIndex (C ⊔ P) = 4 := by rw [sup_comm, h1, hP]
  rw [h4] at h2
  have hne : (C ⊔ P).relIndex T ≠ 0 := relIndex_ne_zero_of_finite _ _
  have h3 : (C ⊔ P).relIndex T = 1 := by omega
  exact le_antisymm hle2 (Subgroup.relIndex_eq_one.1 h3)

variable {x z : G}

theorem aut_facts (h : Hyp2 H T M V) (hTmax : IsMaxSubgroupIn H T)
    (hlt : (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8)
    (d : DihedralPair H T V (V ⊓ pCoreOf 2 H) x z) :
    (∀ t ∈ T, ∀ b ∈ V ⊓ pCoreOf 2 H, t * b * t⁻¹ * b⁻¹ ∈ dpZ V z) ∧
      ∀ ζ ∈ dpZ V z, ∀ g ∈ H, g * ζ = ζ * g := by
  obtain ⟨h3, hZ2, hCA⟩ := pair_counts h d
  set B := V ⊓ pCoreOf 2 H with hB
  set P := dpP H V B z with hP
  set C := T ⊓ Subgroup.centralizer (V : Set G) with hC
  have hPT : P ≤ T := d.PR.trans d.RT
  have hPC : P ⊓ Subgroup.centralizer (V : Set G) = B := inf_centralizer_dpP d hCA
  have hUcard : Nat.card B = 8 := by
    have := d.cardV
    rw [h.V16] at this
    omega
  have hPcard : Nat.card P = 32 := by
    have := (d.isExtraspecialPlus h.V16 hZ2 hCA).2.1
    simpa [hP] using this
  have hCP : C ⊓ P = B := by
    ext g
    constructor
    · intro hg
      have : g ∈ P ⊓ Subgroup.centralizer (V : Set G) := ⟨hg.2, hg.1.2⟩
      rwa [hPC] at this
    · intro hg
      have : g ∈ P ⊓ Subgroup.centralizer (V : Set G) := hPC ▸ hg
      exact ⟨⟨hPT this.1, this.2⟩, this.1⟩
  have hrel : C.relIndex P = 4 := by
    have h1 := Subgroup.relIndex_mul_card C P
    rw [hCP, hUcard, hPcard] at h1
    omega
  have hsup := sup_eq_of_relIndex_lt hPT h.hyp.normal_T hrel hlt
  have hCN : P ≤ Subgroup.normalizer (C : Set G) :=
    hPT.trans (le_normalizer_centralizer h.hyp.normal_T)
  have hdec : ∀ t ∈ T, ∃ c ∈ C, ∃ p ∈ P, t = c * p := by
    intro t ht
    have ht' : t ∈ ((C ⊔ P : Subgroup G) : Set G) := by rw [hsup]; exact ht
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C P hCN] at ht'
    obtain ⟨c, hc, p, hp, rfl⟩ := ht'
    exact ⟨c, hc, p, hp, rfl⟩
  have hpV : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V := fun p hp v hv =>
    (Subgroup.mem_normalizer_iff.mp (h.hyp.normal_T (hPT hp)) v).mp hv
  have hBP : B ≤ P := le_sup_left
  have hTB : ∀ t ∈ T, ∀ b ∈ B, t * b * t⁻¹ * b⁻¹ ∈ dpZ V z := by
    intro t ht b hb
    obtain ⟨c, hc, p, hp, rfl⟩ := hdec t ht
    have hcpb : c * (p * b * p⁻¹) * c⁻¹ = p * b * p⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 hc.2 _ (hpV p hp b hb.1)
      calc c * (p * b * p⁻¹) * c⁻¹ = (c * (p * b * p⁻¹)) * c⁻¹ := rfl
        _ = ((p * b * p⁻¹) * c) * c⁻¹ := by rw [← this]
        _ = p * b * p⁻¹ := by group
    have e : c * p * b * (c * p)⁻¹ * b⁻¹ = (c * (p * b * p⁻¹) * c⁻¹) * b⁻¹ := by group
    rw [e, hcpb]
    exact d.comm_mem_Z hp (hBP hb)
  refine ⟨hTB, ?_⟩
  have hTZ : ∀ ζ ∈ dpZ V z, ∀ t ∈ T, t * ζ = ζ * t := by
    intro ζ hζ t ht
    obtain ⟨c, hc, p, hp, rfl⟩ := hdec t ht
    have h1 : c * ζ = ζ * c := (Subgroup.mem_centralizer_iff.1 hc.2 ζ hζ.1).symm
    have h2 : p * ζ = ζ * p := d.ZC ζ hζ p ((d.PR.trans inf_le_left) hp)
    calc c * p * ζ = c * (p * ζ) := by group
      _ = c * (ζ * p) := by rw [h2]
      _ = (c * ζ) * p := by group
      _ = (ζ * c) * p := by rw [h1]
      _ = ζ * (c * p) := by group
  intro ζ hζ g hg
  set L : Subgroup G := Subgroup.centralizer ((dpZ V z : Subgroup G) : Set G) ⊓ H with hL
  have hTL : T ≤ L := fun t ht =>
    ⟨Subgroup.mem_centralizer_iff.2 fun ζ hζ => (hTZ ζ hζ t ht).symm, d.TH ht⟩
  have hzL : z ∈ L :=
    ⟨Subgroup.mem_centralizer_iff.2 fun ζ hζ => (d.ZC ζ hζ z d.zI).symm, d.zH⟩
  have hzT : z ∉ T := by
    intro hzT
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one d.T2 hzT
    exact d.z1 (eq_one_of_odd_orderOf_of_pow_two_pow d.zodd hk)
  have hLH : L ≤ H := inf_le_right
  have hLeq : L = H := by
    refine hTmax.2 L (lt_of_le_of_ne hTL fun hLT => hzT (hLT ▸ hzL)) hLH
  have hgL : g ∈ L := hLeq ▸ hg
  exact (Subgroup.mem_centralizer_iff.1 hgL.1 ζ hζ).symm

end E217L27

end CFSG.Quasithin
