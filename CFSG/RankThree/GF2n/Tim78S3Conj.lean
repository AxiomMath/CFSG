module

public import CFSG.RankThree.GF2n.Tim78S3Pair
public import CFSG.RankThree.GF2n.Tim78P214

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace NCPair

variable {U V : Subgroup G} (P : NCPair U V) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include P hCen hU

theorem conj_mem_N {x n : G} (hx : x ∈ U ⊔ V)
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    x * n * x⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V :=
  (Subgroup.mem_normalizer_iff.mp (P.le_normalizer hCen hU hx) n).mp hn

theorem omega_conj_le_N {x : G} (hx : x ∈ U ⊔ V) :
    PartTwo.omegaOneSub (conjSubgroup x U) ≤ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V := by
  rw [omegaOneSub_conj P.setup.comm]
  intro z hz
  rw [mem_conjSubgroup] at hz
  have := P.conj_mem_N hCen hU hx (Subgroup.mem_sup_left hz)
  rwa [show x * (x⁻¹ * z * x) * x⁻¹ = z by group] at this

theorem cent_conj {x d m : G} (hx : x ∈ U ⊔ V) (hd : d ∈ conjSubgroup x U)
    (hdL : d ∉ PartTwo.omegaOneSub (conjSubgroup x U))
    (hm : m ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) (hc : d * m = m * d) :
    m ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  rw [omegaOneSub_conj P.setup.comm, mem_conjSubgroup] at hdL ⊢
  have hd' := mem_conjSubgroup.mp hd
  have hm' := P.conj_mem_N hCen hU ((U ⊔ V).inv_mem hx) hm
  rw [inv_inv] at hm'
  refine P.cent hCen hU hd' hdL hm' ?_
  calc x⁻¹ * d * x * (x⁻¹ * m * x) = x⁻¹ * (d * m) * x := by group
    _ = x⁻¹ * (m * d) * x := by rw [hc]
    _ = x⁻¹ * m * x * (x⁻¹ * d * x) := by group

theorem comm_mem_conj {x c m : G} (hx : x ∈ U ⊔ V) (hc : c ∈ conjSubgroup x U)
    (hm : m ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    c * m * c⁻¹ * m⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  rw [omegaOneSub_conj P.setup.comm, mem_conjSubgroup]
  have hc' := mem_conjSubgroup.mp hc
  have hm' := P.conj_mem_N hCen hU ((U ⊔ V).inv_mem hx) hm
  rw [inv_inv] at hm'
  have := P.comm_mem hCen hU hc' hm'
  rwa [show x⁻¹ * c * x * (x⁻¹ * m * x) * (x⁻¹ * c * x)⁻¹ * (x⁻¹ * m * x)⁻¹ =
    x⁻¹ * (c * m * c⁻¹ * m⁻¹) * x by group] at this

theorem exists_not_mem_N {x : G} (hx : x ∈ U ⊔ V) :
    ∃ d ∈ conjSubgroup x U, d ∉ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V := by
  obtain ⟨u, huU, hu2⟩ := P.setup.exp_ne
  refine ⟨x * u * x⁻¹, ?_, fun h => hu2 ?_⟩
  · rw [mem_conjSubgroup, show x⁻¹ * (x * u * x⁻¹) * x = u by group]
    exact huU
  · have h' := P.conj_mem_N hCen hU ((U ⊔ V).inv_mem hx) h
    rw [inv_inv, show x⁻¹ * (x * u * x⁻¹) * x = u by group] at h'
    have := (P.setup.mem_L₀).mp (P.mem_U₀_of_mem_N hCen hU huU h')
    rw [sq]
    exact this.2

theorem centN_conj {x m : G} (hx : x ∈ U ⊔ V)
    (hm : m ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)
    (hcm : ∀ d ∈ conjSubgroup x U, d * m = m * d) :
    m ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  obtain ⟨d, hd, hdN⟩ := P.exists_not_mem_N hCen hU hx
  exact P.cent_conj hCen hU hx hd (fun h => hdN (P.omega_conj_le_N hCen hU hx h)) hm (hcm d hd)

theorem eq_of_le_sup_of_cent {D : Subgroup G} (hDg : ∃ g : G, D = conjSubgroup g U) {x' : G}
    (hx' : x' ∈ U ⊔ V)
    (hD : ∀ m ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V, (∀ d ∈ D, d * m = m * d) →
      m ∈ PartTwo.omegaOneSub D)
    (hle : D ≤ conjSubgroup x' U ⊔ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)) :
    D = conjSubgroup x' U := by
  set N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V with hN
  have hEc := Tim78.comm_conj P.setup.comm x'
  have hEN : conjSubgroup x' U ≤ Subgroup.normalizer (N : Set G) := fun e he =>
    P.le_normalizer hCen hU (by
      rw [show e = x' * (x'⁻¹ * e * x') * x'⁻¹ by group]
      exact (U ⊔ V).mul_mem ((U ⊔ V).mul_mem hx' (Subgroup.mem_sup_left (mem_conjSubgroup.mp he)))
        ((U ⊔ V).inv_mem hx'))
  have hE₀ : PartTwo.omegaOneSub (conjSubgroup x' U) ≤ PartTwo.omegaOneSub D := by
    intro z hz
    have hzN : z ∈ N := P.omega_conj_le_N hCen hU hx' hz
    have hzE : z ∈ conjSubgroup x' U := PartTwo.omegaOneSub_le _ hz
    refine hD z hzN fun d hd => ?_
    obtain ⟨n, hn, e, he, rfl⟩ := exists_mul_of_mem_sup hEN (by rw [sup_comm]; exact hle hd)
    have h1 : z * e = e * z := hEc _ hzE _ he
    have h2 : n * z = z * n := P.comm_N hCen hU hn hzN
    calc n * e * z = n * (e * z) := by group
      _ = n * (z * e) := by rw [h1]
      _ = (n * z) * e := by group
      _ = (z * n) * e := by rw [h2]
      _ = z * (n * e) := by group
  have hE₀1 : PartTwo.omegaOneSub (conjSubgroup x' U) ≠ ⊥ := by
    rw [omegaOneSub_conj P.setup.comm]
    intro h
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (show PartTwo.omegaOneSub U ≠ ⊥ from fun h' => P.setup.ne_bot (by
        rw [eq_bot_iff]
        intro w hw
        rw [← h', ← P.nrm_eq hCen hU]
        exact hw))
    apply hu1
    have : x' * u * x'⁻¹ ∈ conjSubgroup x' (PartTwo.omegaOneSub U) := by
      rw [mem_conjSubgroup, show x'⁻¹ * (x' * u * x'⁻¹) * x' = u by group]
      exact hu
    rw [h, Subgroup.mem_bot] at this
    have hu' : u = 1 := by
      calc u = x'⁻¹ * (x' * u * x'⁻¹) * x' := by group
        _ = 1 := by rw [this]; group
    exact Subtype.ext hu'
  obtain ⟨g, rfl⟩ := hDg
  refine Tim77.conjSubgroup_eq_of_inf_ne_bot P.setup.ti fun hbot => hE₀1 ?_
  rw [eq_bot_iff]
  intro z hz
  rw [← hbot]
  exact Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le _ (hE₀ hz), PartTwo.omegaOneSub_le _ hz⟩

theorem eq_of_le_sup {x x' : G} (hx : x ∈ U ⊔ V) (hx' : x' ∈ U ⊔ V)
    (hle : conjSubgroup x U ≤
      conjSubgroup x' U ⊔ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)) :
    conjSubgroup x U = conjSubgroup x' U :=
  P.eq_of_le_sup_of_cent hCen hU ⟨x, rfl⟩ hx' (fun _ hm hcm => P.centN_conj hCen hU hx hm hcm) hle

theorem exists_conj : ∃ x ∈ U ⊔ V, V = conjSubgroup x U := by
  obtain ⟨g, hg⟩ := P.setup.conj
  have D := P.qdata hCen hU
  have hN := D.normal_Q
  obtain ⟨xq, hxq⟩ := D.quotPair.exists_conj_eq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ xq
  rw [QData.conj_image] at hxq
  have hle : V ≤ conjSubgroup (x : G) U ⊔ (PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) := by
    intro v hv
    have hvX : v ∈ U ⊔ V := Subgroup.mem_sup_right hv
    have hmem : QuotientGroup.mk' (Subgroup.subgroupOf (nrm U V ⊔ nrm V U) (U ⊔ V))
        (⟨v, hvX⟩ : ↥(U ⊔ V)) ∈ (V.subgroupOf (U ⊔ V)).map
          (QuotientGroup.mk' (Subgroup.subgroupOf (nrm U V ⊔ nrm V U) (U ⊔ V))) :=
      ⟨⟨v, hvX⟩, hv, rfl⟩
    rw [hxq] at hmem
    obtain ⟨w, hw, hwv⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hwv
    have hq := QuotientGroup.eq.mp hwv
    rw [Subgroup.mem_subgroupOf, P.N_eq hCen hU] at hq
    have hq' : (w : G)⁻¹ * v ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V := by
      simpa using hq
    rw [show v = (w : G) * ((w : G)⁻¹ * v) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hw))
      (Subgroup.mem_sup_right hq')
  refine ⟨x, x.2, P.eq_of_le_sup_of_cent hCen hU ⟨g, hg⟩ x.2 (fun m hm hcm => ?_) hle⟩
  obtain ⟨v, hv, hv2⟩ := P.setup.exp_ne₁
  have hvL : v ∉ PartTwo.omegaOneSub V := fun h =>
    hv2 (by rw [sq]; exact ((mem_omegaOneSub_iff P.setup.comm₁).mp h).2)
  exact P.symm.cent hCen hU hv hvL (by rwa [sup_comm]) (hcm v hv)

theorem eq_of_le_pGroup {x x' : G} (hx : x ∈ U ⊔ V) (hx' : x' ∈ U ⊔ V) {R : Subgroup G}
    (hR : IsPGroup 2 R) (h1 : conjSubgroup x U ≤ R) (h2 : conjSubgroup x' U ≤ R) :
    conjSubgroup x U = conjSubgroup x' U := by
  have hDc := Tim78.comm_conj P.setup.comm x
  have hD2 : IsPGroup 2 (conjSubgroup x U) := P.setup.two.map (MulAut.conj x).toMonoidHom
  have hDTI : IsTI (conjSubgroup x U) := isTI_conjSubgroup P.setup.ti x
  obtain ⟨u, huU, hu2⟩ := P.setup.exp_ne
  have hxu : x * u * x⁻¹ ∈ conjSubgroup x U := by
    rw [mem_conjSubgroup, show x⁻¹ * (x * u * x⁻¹) * x = u by group]
    exact huU
  have hxu2 : (x * u * x⁻¹) ^ 2 ≠ 1 := fun h => hu2 (by
    rw [conj_pow] at h
    calc u ^ 2 = x⁻¹ * (x * u ^ 2 * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have hk : conjSubgroup (x' * x⁻¹) (conjSubgroup x U) = conjSubgroup x' U := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hcomm := commute_of_conj_le hDc hD2 hDTI hxu hxu2 hR h1 (g := 1) (k := x' * x⁻¹)
    (by rw [conjSubgroup_one]; exact h1) (by rw [hk]; exact h2)
  obtain ⟨v, hv, hvN⟩ := P.exists_not_mem_N hCen hU hx
  obtain ⟨w, hw, hwN⟩ := P.exists_not_mem_N hCen hU hx'
  have hvw : v * w = w * v :=
    hcomm v (by rw [conjSubgroup_one]; exact hv) w (by rw [hk]; exact hw)
  exact P.eq_of_commute hCen hU hx hx' hv hvN hw hwN
    (by rw [hvw, mul_inv_cancel]; exact Subgroup.one_mem _)

theorem exists_fixed {y : G} (hy2 : y * y = 1)
    (hyX : y ∈ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G))
    (hyU : ∃ x ∈ U ⊔ V, conjSubgroup y U = conjSubgroup x U) :
    ∃ x ∈ U ⊔ V, conjSubgroup y (conjSubgroup x U) = conjSubgroup x U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := U ⊔ V with hX
  let St : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (X : Set G) ∧
        ∃ x ∈ X, conjSubgroup g U = conjSubgroup x U}
      one_mem' := ⟨Subgroup.one_mem _, 1, X.one_mem, rfl⟩
      mul_mem' := fun {g h} hg hh => ⟨Subgroup.mul_mem _ hg.1 hh.1, by
        obtain ⟨xg, hxg, eg⟩ := hg.2
        obtain ⟨xh, hxh, eh⟩ := hh.2
        refine ⟨g * xh * g⁻¹ * xg,
          X.mul_mem ((Subgroup.mem_normalizer_iff.mp hg.1 xh).mp hxh) hxg, ?_⟩
        calc conjSubgroup (g * h) U = conjSubgroup g (conjSubgroup xh U) := by
              rw [conjSubgroup_mul, eh]
          _ = conjSubgroup (g * xh * g⁻¹) (conjSubgroup g U) := by
              rw [← conjSubgroup_mul, ← conjSubgroup_mul]
              congr 1
              group
          _ = conjSubgroup (g * xh * g⁻¹ * xg) U := by rw [eg, ← conjSubgroup_mul]⟩
      inv_mem' := fun {g} hg => ⟨Subgroup.inv_mem _ hg.1, by
        obtain ⟨xg, hxg, eg⟩ := hg.2
        refine ⟨g⁻¹ * xg⁻¹ * g, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg.1) xg⁻¹).mp
            (X.inv_mem hxg)
          rwa [inv_inv] at this
        · have hn : conjSubgroup (xg⁻¹ * g) U = U := by
            rw [conjSubgroup_mul, eg, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
          have hn' : conjSubgroup (g⁻¹ * xg) U = U := by
            rw [conjSubgroup_eq_self_iff] at hn ⊢
            have := Subgroup.inv_mem _ hn
            rwa [mul_inv_rev, inv_inv] at this
          calc conjSubgroup g⁻¹ U = conjSubgroup ((g⁻¹ * xg⁻¹ * g) * (g⁻¹ * xg)) U := by
                congr 1
                group
            _ = conjSubgroup (g⁻¹ * xg⁻¹ * g) (conjSubgroup (g⁻¹ * xg) U) :=
                conjSubgroup_mul _ _ _
            _ = conjSubgroup (g⁻¹ * xg⁻¹ * g) U := by rw [hn']⟩ }
  have hXSt : X ≤ St := fun x hx => ⟨Subgroup.le_normalizer hx, x, hx, rfl⟩
  have hySt : y ∈ St := ⟨hyX, hyU⟩
  set K := X ⊔ Subgroup.zpowers y with hK
  have hKSt : K ≤ St := sup_le hXSt ((Subgroup.zpowers_le).mpr hySt)
  have hy' : IsPGroup 2 ((Subgroup.zpowers y).subgroupOf K) := by
    have h0 : IsPGroup 2 (Subgroup.zpowers y) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (orderOf_dvd_of_pow_eq_one (show y ^ 2 ^ 1 = 1 by rw [pow_one, sq]; exact hy2))
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    exact h0.comap_of_injective _ Subtype.val_injective
  obtain ⟨P₂, hP₂⟩ := hy'.exists_le_sylow
  have hU' : IsPGroup 2 (U.subgroupOf K) :=
    P.setup.two.comap_of_injective _ Subtype.val_injective
  obtain ⟨P₁, hP₁⟩ := hU'.exists_le_sylow
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq (↥K) P₁ P₂
  have hzSt := hKSt z.2
  obtain ⟨x, hx, hzx⟩ := hzSt.2
  set R : Subgroup G := ((P₂ : Subgroup ↥K).map K.subtype) ⊓ X with hR
  have hR2 : IsPGroup 2 R := (P₂.isPGroup'.map K.subtype).to_inf_left
  have hyP : y ∈ (P₂ : Subgroup ↥K).map K.subtype :=
    ⟨⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩,
      hP₂ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)), rfl⟩
  have hyR : y ∈ Subgroup.normalizer (R : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hyP) hyX
  have hDR : conjSubgroup (z : G) U ≤ R := by
    intro d hd
    have hd' := mem_conjSubgroup.mp hd
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine ⟨⟨d, ?_⟩, ?_, rfl⟩
      · rw [show d = (z : G) * ((z : G)⁻¹ * d * z) * (z : G)⁻¹ by group]
        exact K.mul_mem (K.mul_mem z.2 (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd')))
          (K.inv_mem z.2)
      · rw [← hz, SetLike.mem_coe, mem_smul_sylow_iff]
        apply hP₁
        rw [Subgroup.mem_subgroupOf]
        exact hd'
    · rw [show d = (z : G) * ((z : G)⁻¹ * d * z) * (z : G)⁻¹ by group]
      exact (Subgroup.mem_normalizer_iff.mp (hKSt z.2).1 _).mp (Subgroup.mem_sup_left hd')
  rw [hzx] at hDR
  have hyx := Subgroup.mul_mem _ hySt (hXSt hx)
  obtain ⟨x'', hx'', hyxe⟩ := hyx.2
  have hER : conjSubgroup x'' U ≤ R := by
    rw [← hyxe, conjSubgroup_mul]
    intro e he
    rw [mem_conjSubgroup] at he
    have := (Subgroup.mem_normalizer_iff.mp hyR _).mp (hDR he)
    rwa [show y * (y⁻¹ * e * y) * y⁻¹ = e by group] at this
  refine ⟨x, hx, ?_⟩
  rw [← conjSubgroup_mul, hyxe]
  exact (P.eq_of_le_pGroup hCen hU hx hx'' hR2 hDR hER).symm

end NCPair

end CFSG.RankThree.GF2n.Tim78
