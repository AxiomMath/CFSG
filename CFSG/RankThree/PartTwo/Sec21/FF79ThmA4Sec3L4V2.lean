module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4KW
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4V
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MFacts
import CFSG.Walter.W67.W1Basic
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Comp
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4KA5

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem v_elem_sub {X Y : Subgroup G} (hY : IsElementaryAbelian 3 ↥Y) (h : X ≤ Y) :
    IsElementaryAbelian 3 ↥X := by
  refine
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
        (v_comm hY.toIsMulCommutative (h x.2) (h y.2))⟩⟩
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => Subtype.ext ?_
  exact elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := Y) (g : G) (h g.2)

theorem v_K_ord3 {K : Subgroup G} (hK : IsLnq 2 2 2 K) : ∃ x ∈ K, orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h60 := (M42A5.of_IsLnq hK).card
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 (by rw [h60]; norm_num)
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

theorem v_K_not_central {K : Subgroup G} (hK : IsLnq 2 2 2 K) {x : G} (hx : x ∈ K)
    (hxo : orderOf x = 3) : ¬ ∀ y ∈ K, x * y = y * x := by
  intro hc
  have hsimple := (M42A5.of_IsLnq hK).simple
  have h60 := (M42A5.of_IsLnq hK).card
  set z : ↥K := ⟨x, hx⟩ with hz
  have hzo : orderOf z = 3 := by rw [hz, Subgroup.orderOf_mk, hxo]
  haveI : (Subgroup.zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * z = z * g := (Subtype.ext (hc g.1 g.2)).symm
    have h2 : g * z ^ k * g⁻¹ = z ^ k := by
      have : g * z * g⁻¹ = z := by rw [this]; group
      rw [← conj_zpow, this]
    rw [h2]; exact Subgroup.zpow_mem_zpowers z k
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers z) with h | h
  · have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hzo
    omega
  · have := Subgroup.card_top (G := ↥K)
    rw [← h, Nat.card_zpowers, hzo, h60] at this
    omega

theorem v_exists_sylow_ge {Q : Subgroup G} (hQ : IsPGroup 3 Q) :
    ∃ S : Subgroup G, IsSylowOf 3 S ⊤ ∧ Q ≤ S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := L41.exists_sylowOf_p (p := 3) (⊤ : Subgroup G)
  obtain ⟨k, -, hk⟩ := L41.exists_conj_le_sylowOf_p hP le_top hQ
  refine ⟨conjBy k⁻¹ P, ?_, fun x hx => ?_⟩
  · have := L41.isSylowOf_conjBy hP k⁻¹
    have e : conjBy k⁻¹ (⊤ : Subgroup G) = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [L41.card_conjBy, Subgroup.card_top]
    rwa [e] at this
  · refine ⟨k * x * k⁻¹, hk x hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

section VStructure

variable {b : G} {J B A P D : Subgroup G}

theorem v_zpowers_le_nor {x y : G} (h : x * y = y * x) :
    Subgroup.zpowers x ≤ Nor (Subgroup.zpowers y) := by
  have hx : x ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (Commute.symm h) m).eq
  exact (Subgroup.zpowers_le).mpr (Subgroup.centralizer_le_normalizer _ hx)

theorem v_closure_pair (a b : G) :
    Subgroup.closure {a, b} = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
    Set.singleton_union]

theorem v_nab_inf (h : FF79Sec34In4 b J B A P D) (hbJ : b ∉ J) {a : G} (ha : a ∈ B ⊓ J) :
    Subgroup.closure {a, b} ⊓ (B ⊓ J) ≤ Subgroup.zpowers a := by
  have hB := h.elemB.1.toIsMulCommutative
  have hbB : b ∈ B := h.supB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hab : a * b = b * a := v_comm hB ha.1 hbB
  have hbB0 : b ∉ B ⊓ J := fun hh => hbJ hh.2
  have hinf := v_zpowers_inf_eq_bot h.hyp.ord hbB0
  rintro c ⟨hc, hcB⟩
  rw [v_closure_pair] at hc
  have hc' : c ∈ (↑(Subgroup.zpowers a ⊔ Subgroup.zpowers b) : Set G) := hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (v_zpowers_le_nor hab)] at hc'
  obtain ⟨u, hu, w, hw, rfl⟩ := hc'
  have huB : u ∈ B ⊓ J := (Subgroup.zpowers_le.mpr ha) hu
  have hwB : w ∈ B ⊓ J := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ huB) hcB
    simpa using this
  have : w ∈ Subgroup.zpowers b ⊓ (B ⊓ J) := ⟨hw, hwB⟩
  rw [hinf, Subgroup.mem_bot] at this
  show u * w ∈ _
  rw [this, mul_one]
  exact hu

theorem v_nor_iff (h : FF79Sec34In4 b J B A P D) (hbJ : b ∉ J) {a : G} (ha : a ∈ B ⊓ J)
    {x : G} (hx : x ∈ A) :
    x ∈ Nor (Subgroup.closure {a, b}) ↔ ⁅b, x⁆ ∈ Subgroup.zpowers a := by
  have hB := h.elemB.1.toIsMulCommutative
  have hbB : b ∈ B := h.supB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hA := h.elemA.1.toIsMulCommutative
  have hbN : b ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (by simp)
  have haN : a ∈ Subgroup.closure {a, b} := Subgroup.subset_closure (by simp)
  constructor
  · intro hxN
    have h1 : b * (x * b⁻¹ * x⁻¹) ∈ Subgroup.closure {a, b} := by
      refine Subgroup.mul_mem _ hbN ?_
      exact (Subgroup.mem_normalizer_iff.mp hxN b⁻¹).mp (Subgroup.inv_mem _ hbN)
    have h2 : ⁅b, x⁆ ∈ (B ⊓ J) := by
      rw [← h.commbA]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) hx
    apply v_nab_inf h hbJ ha
    refine ⟨?_, h2⟩
    have e : ⁅b, x⁆ = b * (x * b⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]; exact h1
  · intro hc
    have hc' : ⁅b, x⁆ ∈ Subgroup.closure {a, b} :=
      (Subgroup.zpowers_le.mpr haN) hc
    have hxa : x * a * x⁻¹ = a := by
      have := v_comm hA hx (h.B0A ha)
      rw [this]; group
    have hxb : x * b * x⁻¹ = (⁅b, x⁆)⁻¹ * b := by
      simp only [commutatorElement_def]; group
    have hle : Subgroup.closure {a, b} ≤
        (Subgroup.closure {a, b}).comap (MulAut.conj x).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases hy with rfl | hy
      · show _ ∈ Subgroup.closure {y, b}
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxa]
        exact haN
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        show _ ∈ Subgroup.closure {a, y}
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxb]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc') hbN
    refine L41.mem_nor_of_forall fun y hy => ?_
    exact hle hy

theorem v_V_card (h : FF79Sec34In4 b J B A P D) (hbJ : b ∉ J) {a : G} (ha : a ∈ B ⊓ J)
    (hoa : orderOf a = 3) :
    Nat.card (A ⊓ Nor (Subgroup.closure {a, b}) : Subgroup G) = 27 := by
  have hA := h.elemA.1.toIsMulCommutative
  set φ := vCommMap hA h.bA with hφ
  have hφx : ∀ x : A, φ x = ⁅b, (x : G)⁆ := fun x => v_commMap_apply hA h.bA x
  have hrange : φ.range = B ⊓ J := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hφx, ← h.commbA]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) x.2
    · rw [← h.commbA]
      exact v_comm_le_range hA h.bA
  set H : Subgroup ↥A := (Subgroup.zpowers a).comap φ with hH
  have hza : Subgroup.zpowers a ≤ B ⊓ J := Subgroup.zpowers_le.mpr ha
  have hindex : H.index = 3 := by
    rw [hH, Subgroup.index_comap, hrange]
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers a) (K := B ⊓ J)
    rw [inf_of_le_left hza, Nat.card_zpowers, hoa, h.elemB0.2] at h1
    omega
  have hcardH : Nat.card H = 27 := by
    have h1 := Subgroup.card_mul_index H
    rw [hindex, h.elemA.2] at h1
    omega
  rw [← hcardH]
  refine Nat.card_congr
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, ?_⟩
      invFun := fun y => ⟨y.1.1, y.1.2, ?_⟩
      left_inv := fun v => rfl
      right_inv := fun y => rfl }
  · exact (v_nor_iff h hbJ ha v.2.1).mp v.2.2
  · exact (v_nor_iff h hbJ ha y.1.2).mpr y.2

theorem v_cenS_nor {K : Subgroup G} {b : G} (hKb : ∀ k ∈ K, b * k = k * b) : b ∈ Nor (CenS K) := by
  refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
  have e2 : ∀ k ∈ K, b⁻¹ * k * b = k := fun k hk => by
    have := hKb k hk
    calc b⁻¹ * k * b = b⁻¹ * (k * b) := by group
      _ = b⁻¹ * (b * k) := by rw [this]
      _ = k := by group
  have e1 : ∀ k ∈ K, b * k * b⁻¹ = k := fun k hk => by
    have := hKb k hk
    rw [this]; group
  constructor
  · intro hy
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have h1 := (Subgroup.mem_centralizer_iff.mp hy) k hk
    calc k * (b * y * b⁻¹) = (b * k * b⁻¹) * (b * y * b⁻¹) := by rw [e1 k hk]
      _ = b * (k * y) * b⁻¹ := by group
      _ = b * (y * k) * b⁻¹ := by rw [h1]
      _ = (b * y * b⁻¹) * (b * k * b⁻¹) := by group
      _ = (b * y * b⁻¹) * k := by rw [e1 k hk]
  · intro hy
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have h1 := (Subgroup.mem_centralizer_iff.mp hy) k hk
    calc k * y = (b⁻¹ * k * b) * y := by rw [e2 k hk]
      _ = b⁻¹ * (k * (b * y * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * y * b⁻¹) * k) * b := by rw [h1]
      _ = y * (b⁻¹ * k * b) := by group
      _ = y * k := by rw [e2 k hk]

theorem v_nor_inf {X Y : Subgroup G} {b : G} (hX : b ∈ Nor X) (hY : b ∈ Nor Y) :
    b ∈ Nor (X ⊓ Y) := by
  refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
  have h1 := Subgroup.mem_normalizer_iff.mp hX y
  have h2 := Subgroup.mem_normalizer_iff.mp hY y
  exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩

theorem v_B0_not_cen (h : FF79Sec34In4 b J B A P D) (hbJ : b ∉ J) {a : G}
    (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) : ¬ (B ⊓ J ≤ CenS (Lay (J ⊓ Cen a))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hcen
  have hB := h.elemB.1.toIsMulCommutative
  have hbB : b ∈ B := h.supB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hJcen : J ≤ Cen b := h.hyp.std.1
  obtain ⟨x, hxK, hxo⟩ := v_K_ord3 hK
  have hxJ : x ∈ J := (lay_le _ hxK).1
  have hxb : x ∈ Cen b := hJcen hxJ
  have hxc : ∀ y ∈ B ⊓ J, y * x = x * y := fun y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hcen hy)) x hxK).symm
  have hxB0 : x ∉ B ⊓ J := fun hx =>
    v_K_not_central hK hxK hxo fun y hy => by
      exact ((Subgroup.mem_centralizer_iff.mp (hcen hx)) y hy).symm
  have hinf : (B ⊓ J) ⊓ Subgroup.zpowers x = ⊥ := by
    rw [inf_comm]; exact v_zpowers_inf_eq_bot hxo hxB0
  set T1 : Subgroup G := (B ⊓ J) ⊔ Subgroup.zpowers x with hT1
  have hcomm : ∀ y ∈ (B ⊓ J), ∀ z ∈ Subgroup.zpowers x, y * z = z * y := by
    intro y hy z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (hxc y hy) n).eq
  have hcard : Nat.card T1 = 27 := by
    obtain ⟨h1, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [hinf, Subgroup.card_bot, mul_one, h.elemB0.2, Nat.card_zpowers, hxo] at h1
    simpa using h1
  have hT3 : IsPGroup 3 T1 := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hzb : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.hyp.ord]; norm_num)
  have hT1b : ∀ t ∈ T1, b * t = t * b := by
    have : T1 ≤ Cen b := by
      refine sup_le (fun y hy => ?_) ((Subgroup.zpowers_le).mpr hxb)
      exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw; subst hw; exact v_comm hB hbB hy.1
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (this ht)) b rfl
  have hT1nor : T1 ≤ Nor (Subgroup.zpowers b) := by
    intro t ht
    exact v_zpowers_le_nor (hT1b t ht).symm (Subgroup.mem_zpowers t)
  have hsup3 : IsPGroup 3 (T1 ⊔ Subgroup.zpowers b : Subgroup G) :=
    hT3.to_sup_of_normal_right' hzb hT1nor
  obtain ⟨S, hS, hSle⟩ := v_exists_sylow_ge hsup3
  have hbS : b ∈ S := hSle (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hT1S : T1 ≤ S := le_trans le_sup_left hSle
  have hT1cen : T1 ≤ Cen b := by
    intro t ht
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff] at hw; subst hw; exact hT1b t ht
  have hbT1 := (sec34_cenb_syl h S hS hbS T1 hT1S hT1cen).2 hcard
  have hT1J : T1 ≤ J := sup_le inf_le_right ((Subgroup.zpowers_le).mpr hxJ)
  exact hbJ (hT1J hbT1)

theorem sec34_UFacts (hs : FF79Sec3 b J) (h : FF79Sec34In4 b J B A P D) {a : G}
    (ha : a ∈ B ⊓ J) (hoa : orderOf a = 3) (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) :
    FF79Sec34UFacts b a J A := by
  have hbJ : b ∉ J := fun hh => hs.notConj ⟨1, by simpa using hh⟩
  have hB := h.elemB.1.toIsMulCommutative
  have hbB : b ∈ B := h.supB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hJcen : J ≤ Cen b := h.hyp.std.1
  set K : Subgroup G := Lay (J ⊓ Cen a) with hKdef
  have hKJ : K ≤ J ⊓ Cen a := lay_le _
  have hKb : K ≤ Cen b := fun k hk => hJcen (hKJ hk).1
  have hbK : ∀ k ∈ K, b * k = k * b := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hKb hk)) b rfl
  set Nab : Subgroup G := Subgroup.closure {a, b} with hNab
  have haN : a ∈ Nab := Subgroup.subset_closure (by simp)
  have hbN : b ∈ Nab := Subgroup.subset_closure (by simp)
  set V : Subgroup G := A ⊓ Nor Nab with hV
  have hVcard : Nat.card V = 27 := v_V_card h hbJ ha hoa
  have hVnorK : V ≤ Nor K := fun v hv => sec34_nor_lay h ha.2 hv.2
  have hV3 : IsElementaryAbelian 3 ↥V := v_elem_sub h.elemA.1 inf_le_left
  set U : Subgroup G := U34 b a J A with hU
  have hVU : V ⊓ CenS K = U := by
    ext x
    simp only [hV, hU, Subgroup.mem_inf]
    tauto
  have hUV : U ≤ V := by rw [← hVU]; exact inf_le_left
  have hcard3 : Nat.card V ≤ 3 * Nat.card U := by
    have := sec34_a5_elem3 hK V hVnorK hV3
    rwa [hVU] at this
  have hQ := v_B0_not_cen h hbJ hK
  have hB0V : B ⊓ J ≤ V := by
    intro x hx
    refine ⟨h.B0A hx, (v_nor_iff h hbJ ha (h.B0A hx)).mpr ?_⟩
    have : ⁅b, x⁆ = 1 := by
      rw [commutatorElement_def, v_comm hB hbB hx.1]; group
    rw [this]; exact Subgroup.one_mem _
  have hUne : Nat.card U ≠ 27 := by
    intro h27
    have hUV' : U = V := Subgroup.eq_of_le_of_card_ge hUV (by rw [hVcard, h27])
    apply hQ
    intro x hx
    have : x ∈ U := hUV' ▸ hB0V hx
    exact this.1.2
  have hU9 : Nat.card U = 9 := by
    have hd : Nat.card U ∣ 27 := hVcard ▸ Subgroup.card_dvd_of_le hUV
    have hd' : Nat.card U ∣ 3 ^ 3 := by simpa using hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd'
    interval_cases k
    · omega
    · omega
    · simpa using hk'
    · exact absurd hk' hUne
  have hUA : U ≤ A := fun x hx => hx.1.1
  have haU : a ∈ U := by
    refine ⟨⟨h.B0A ha, ?_⟩, Subgroup.le_normalizer haN⟩
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hKJ hk).2) a rfl).symm
  have hbNU : b ∈ Nor U := by
    have h1 : b ∈ Nor (A ⊓ CenS K) := v_nor_inf h.bA (v_cenS_nor hbK)
    exact v_nor_inf h1 (Subgroup.le_normalizer (Subgroup.le_normalizer hbN))
  have hK_cen_U : K ≤ CenS U := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.mp hu.1.2) x hx |>.symm
  have hcenUb : U ⊓ Cen b = Subgroup.zpowers a := by
    apply le_antisymm
    · set R : Subgroup G := (B ⊓ J) ⊓ CenS K with hR
      have hRle : U ⊓ Cen b ≤ R := by
        rintro x ⟨hxU, hxb⟩
        refine ⟨?_, hxU.1.2⟩
        rw [← v_A_cen h]
        exact ⟨hxU.1.1, hxb⟩
      have hRd : Nat.card R ∣ 3 ^ 2 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : R ≤ B ⊓ J)
        rwa [h.elemB0.2] at this
      have hzR : Subgroup.zpowers a ≤ R := by
        refine Subgroup.zpowers_le.mpr ⟨ha, ?_⟩
        exact (Subgroup.mem_centralizer_iff.mpr fun k hk =>
          ((Subgroup.mem_centralizer_iff.mp (hKJ hk).2) a rfl).symm)
      have hR3 : Nat.card R ≤ 3 := by
        obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hRd
        interval_cases k
        · omega
        · omega
        · exfalso
          apply hQ
          have : R = B ⊓ J := Subgroup.eq_of_le_of_card_ge inf_le_left
            (by rw [h.elemB0.2]; simpa using hk'.ge)
          rw [← this]
          exact inf_le_right
      have hzeq : Subgroup.zpowers a = R := Subgroup.eq_of_le_of_card_ge hzR
        (by rw [Nat.card_zpowers, hoa]; exact hR3)
      rw [← hzeq] at hRle
      exact hRle
    · refine Subgroup.zpowers_le.mpr ⟨haU, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw; subst hw; exact (v_comm hB hbB ha.1 : _) 
  refine ⟨⟨?_, hU9⟩, hUA, haU, hbNU, hcenUb, hK_cen_U, hKb, ?_⟩
  · exact v_elem_sub h.elemA.1 hUA
  · intro w hw
    rw [← sec34_layW h ha.2]
    exact lay_mem_nor hw

end VStructure

end CFSG.RankThree.PartTwo.Sec21.FF79.H4
