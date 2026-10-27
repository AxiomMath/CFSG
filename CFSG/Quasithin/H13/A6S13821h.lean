module

public import CFSG.Quasithin.H13.A6S13821f
public import CFSG.Quasithin.H13.A6S13816m
public import CFSG.Quasithin.H13.A6S13825o
public import CFSG.Quasithin.Vol2.Ch11SecA02Quot

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace A6Hat7

theorem not_isSolvable_of_quasisimple {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  obtain ⟨hperf, -, a, b, hab⟩ := hq
  have : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Subsingleton (Q ⧸ Subgroup.center Q) := Quotient.instSubsingletonQuotient _
    exact hab (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isSolvable Q

theorem le_of_center_three {K : Type} [Group K] [Finite K] {P C : Subgroup K} [P.Normal]
    [hC : C.Normal] (hq : CFSG.IsQuasisimple (K ⧸ P))
    (hZ : Nat.card (Subgroup.center (K ⧸ P)) = 3) (hPC : P ≤ C) {c : K}
    (hcZ : (c : K ⧸ P) ∈ Subgroup.center (K ⧸ P)) (hcC : c ∉ C) : C ≤ P := by
  set π := QuotientGroup.mk' P with hπ
  have hmem : ∀ x : K, π x ∈ C.map π → x ∈ C := by
    rintro x ⟨d, hd, hdx⟩
    have hdx' : d⁻¹ * x ∈ P := by
      rw [← QuotientGroup.eq]
      exact hdx
    have := C.mul_mem hd (hPC hdx')
    simpa using this
  have hcM : π c ∉ C.map π := fun h => hcC (hmem c h)
  have hMn : (C.map π).Normal := hC.map π (QuotientGroup.mk'_surjective P)
  have hMt : C.map π ≠ ⊤ := fun h => hcM (h ▸ Subgroup.mem_top _)
  have hle := Vol2.Ch11.SecA.le_center_of_normal_ne_top hq hMt
  have hdvd : Nat.card ↥(C.map π) ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · intro x hx
    have hx' : π x ∈ C.map π := ⟨x, hx, rfl⟩
    rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).mp hx'
  · exfalso
    have heq : C.map π = Subgroup.center (K ⧸ P) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hZ])
    exact hcM (heq ▸ hcZ)

variable {G : Type} [Group G] [Finite G]

theorem oTwoRes_solvRad_ne_bot {H K : Subgroup G} (hK : K ∈ cComp H)
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) : oTwoRes (solvRad H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := ↥K ⧸ CFSG.pCore 2 ↥K with hQ
  set π : ↥K →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set Z' : Subgroup ↥K := (Subgroup.center Q).comap π with hZ'
  set Zh : Subgroup G := Z'.map K.subtype with hZh
  have hZhK : Zh ≤ K := Subgroup.map_subtype_le _
  have hZ'n : Z'.Normal := (Subgroup.center Q).normal_of_characteristic.comap π
  have hZ's : Group.IsSolvable ↥Z' := by
    have hP : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := by
      have := IsPGroup.isNilpotent (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
      infer_instance
    have hO : CFSG.pCore 2 ↥K ≤ Z' := fun x hx => by
      show π x ∈ Subgroup.center Q
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact Subgroup.one_mem _
    let f : ↥(CFSG.pCore 2 ↥K) →* ↥Z' := Subgroup.inclusion hO
    let g : ↥Z' →* ↥(Subgroup.center Q) := (π.comp Z'.subtype).codRestrict _ fun x => x.2
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro x hx
    have hx1 : π x = 1 := congrArg Subtype.val hx
    exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp hx1⟩, rfl⟩
  have hZhR : Zh ≤ solvRad H := by
    refine (le_solvRad hZhK ?_ ?_).trans
      (solvRad_le_solvRad_of_subnormal (subnormal_of_mem_cComp hK))
    · rw [hZh, map_subtype_subgroupOf']
      exact hZ'n
    · exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective Z' K.subtype
        K.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have h3 : 3 ∣ Nat.card ↥(Subgroup.center Q) := by rw [hZ]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Q)) 3 h3
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) (z : Q)
  have hkZ : k ∈ Z' := by
    show π k ∈ Subgroup.center Q
    rw [hπ, hk]
    exact z.2
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  have hk'm : (k ^ 2 ^ a) ^ m = 1 := by rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hk'1 : π (k ^ 2 ^ a) ≠ 1 := by
    intro h1
    rw [map_pow, hπ, hk] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [Subgroup.orderOf_coe, hz] at h2
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)) (by norm_num)
  have hmem : ((k ^ 2 ^ a : ↥K) : G) ∈ oTwoRes (solvRad H) :=
    mem_oTwoRes_of_odd (hZhR ⟨k ^ 2 ^ a, Z'.pow_mem hkZ _, rfl⟩) hm
      (by rw [← Subgroup.coe_pow, hk'm, Subgroup.coe_one])
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hk'1
  have : k ^ 2 ^ a = 1 := Subtype.ext hmem
  rw [this, map_one]

theorem mem_center_of_mem_solvRad {H K : Subgroup G} (hKH : K ≤ H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {x : ↥K} (hx : (x : G) ∈ solvRad H) :
    (x : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set N : Subgroup ↥K := (solvRad H).subgroupOf K with hN
  have hNn : N.Normal := ⟨fun n hn k => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_solvRad (Subgroup.le_normalizer (hKH k.2)) hn⟩
  have hNs : Group.IsSolvable ↥N := by
    have := solvRad_isSolvable H
    let f : ↥N →* ↥(solvRad H) :=
      { toFun := fun y => ⟨((y : ↥K) : G), Subgroup.mem_subgroupOf.mp y.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun y₁ y₂ h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hMn : (N.map π).Normal := hNn.map π (QuotientGroup.mk'_surjective _)
  have hMt : N.map π ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective (π.comp N.subtype) := fun q => by
      obtain ⟨n, hn, hnq⟩ := (htop ▸ Subgroup.mem_top q : q ∈ N.map π)
      exact ⟨⟨n, hn⟩, hnq⟩
    have : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) := Group.isSolvable_of_surjective hsurj
    exact not_isSolvable_of_quasisimple hq this
  exact Vol2.Ch11.SecA.le_center_of_normal_ne_top hq hMt ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

attribute [local instance] commGroupOfFact in
theorem nonempty_mulEquiv_autIH_of {T V L V₁ Vp H K I : Subgroup G}
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) {c : ↥K}
    (hcZ : (c : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))
    (hcI : ¬ ∀ u ∈ conjClosure I H, (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ V₁) :
    Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autIH V₁ I H K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := factElem h hIU
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (Setting4.pCoreOf_subgroupOf_eq K)) h.K_quasisimple
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  set C := (toAutI h I).ker with hC
  have hPC : CFSG.pCore 2 ↥K ≤ C := by
    intro x hx
    rw [hC, MonoidHom.mem_ker, toAutI_eq_one_iff]
    have hxO : (x : G) ∈ pCoreOf 2 K := by
      rw [← Setting4.pCoreOf_subgroupOf_eq K] at hx
      exact hx
    exact h.actH_eq_one_of_mem_pCoreOf hIU
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h.K_cComp) hxO)
  have hcC : c ∉ C := by
    intro hc
    rw [hC, MonoidHom.mem_ker, toAutI_eq_one_iff,
      A6Tv.actH_eq_one_iff h.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H)] at hc
    exact hcI hc
  have hle := le_of_center_three hq hZ hPC hcZ hcC
  have hker : C = CFSG.pCore 2 ↥K := le_antisymm hle hPC
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toAutI_surjective h I))⟩

end A6Hat7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_c_hat (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hX : oTwoRes (solvRad H) ≠ ⊥) :
    ∃ c : ↥(Subgroup.normalizer (V : Set G)), (c : G) ∈ oTwoRes (solvRad H) ∧
      (c : G) ^ 3 = 1 ∧ S.frame.ρ c = swap 0 1 * swap 1 2 ∧
      (c : G) ∈ Subgroup.normalizer (S.V3 : Set G) ∧
      ∀ h ∈ H, h * (c : G) * h⁻¹ * (c : G)⁻¹ ∈ pCoreOf 2 H ∨
        h * (c : G) * h⁻¹ * (c : G) ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := oTwoRes (solvRad H) with hXdef
  have hHR : H ≤ Subgroup.normalizer (solvRad H : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := A5.le_normalizer_oTwoRes_of_le_normalizer hHR
  have hXH : X ≤ H := (oTwoRes_le _).trans (solvRad_le H)
  have hOX : pCoreOf 2 X ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 X).trans hXH)
      (hHX.trans (normalizer_le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have key : S14.PlusData S X → ∃ c : ↥(Subgroup.normalizer (V : Set G)), (c : G) ∈ X ∧
      (c : G) ^ 3 = 1 ∧ S.frame.ρ c = swap 0 1 * swap 1 2 ∧
      (c : G) ∈ Subgroup.normalizer (S.V3 : Set G) ∧
      ∀ h ∈ H, h * (c : G) * h⁻¹ * (c : G)⁻¹ ∈ pCoreOf 2 H ∨
        h * (c : G) * h⁻¹ * (c : G) ∈ pCoreOf 2 H := by
    intro P
    obtain ⟨c, hcX, hρ, hc3⟩ := P.exists_c012_cube
    refine ⟨c, hcX, hc3, hρ, P.le_NV3 hcX, fun h hh => ?_⟩
    have hcH : (c : G) ∈ H := hXH hcX
    have hx : h * (c : G) * h⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hHX hh) _).mp hcX
    have hccc : (c : G) * c * c = 1 := by rw [← pow_three', hc3]
    rcases P.decomp hcX hρ hx with h1 | h1 | h1
    · exfalso
      apply S14.PlusData.not_mem (Lp := H) hρ hc3
      have h2 := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hh)) _).mp (hOX h1)
      simpa [mul_assoc] using h2
    · left
      have h2 := (Subgroup.mem_normalizer_iff.mp (hHQ hcH) _).mp (hOX h1)
      have e : h * (c : G) * h⁻¹ * (c : G)⁻¹ =
          (c : G) * ((c : G) * c * (h * c * h⁻¹)) * (c : G)⁻¹ := by
        calc h * (c : G) * h⁻¹ * (c : G)⁻¹ = ((c : G) * c * c) * (h * c * h⁻¹) * (c : G)⁻¹ := by
              rw [hccc, one_mul]
          _ = (c : G) * ((c : G) * c * (h * c * h⁻¹)) * (c : G)⁻¹ := by group
      rw [e]
      exact h2
    · right
      have h2 := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hcH)) _).mp (hOX h1)
      have e : h * (c : G) * h⁻¹ * (c : G) =
          (c : G)⁻¹ * ((c : G) * (h * c * h⁻¹)) * (c : G)⁻¹⁻¹ := by group
      rw [e]
      exact h2
  rcases S.oTwoRes_solvRad_cases h139 h1334 h13 hS hH with h | ⟨hh, h⟩ | ⟨hh, h⟩
  · exact absurd h hX
  · exact key (by rw [hXdef, h]; exact S14.plusData_L1 S hh)
  · exact key (by rw [hXdef, h]; exact S14.plusData_l1plus S (S.hatL1Plus hh))

theorem mem_V1_of_fix (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {c : G} (hcH : c ∈ H)
    (hN : ∀ u ∈ conjClosure S.V3 H, u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ∈ fsuV1 T V)
    {u : G} (hu : u ∈ conjClosure S.V3 H) (hfix : c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    u ∈ fsuV1 T V := by
  have hab := L13825.isElemAbelian_UH hS hH
  have hF := (hS.hF H hH).toHypF91
  have hV₁U : fsuV1 T V ≤ conjClosure S.V3 H :=
    (S.V1_le_V2.trans S.V2_le_V3).trans (le_conjClosure S.V3 H)
  set v := c * u * c⁻¹ * u⁻¹ with hv
  have hvV : v ∈ fsuV1 T V := hfix
  set w := c * v * c⁻¹ with hwdef
  have hw : w ∈ fsuV1 T V :=
    (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ hcH) v).mp hvV
  have hcomm : ∀ a ∈ conjClosure S.V3 H, ∀ b ∈ conjClosure S.V3 H, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ conjClosure S.V3 H, a * a = 1 := fun a ha => by
    have := hab.2 a ha
    rwa [pow_two] at this
  have e1 : c * u * c⁻¹ = v * u := by rw [hv]; group
  have e2 : c * (c * u * c⁻¹) * c⁻¹ = w * (v * u) := by rw [hwdef, hv]; group
  have h1 := hN u hu
  rw [e2, e1] at h1
  have hvU := hV₁U hvV
  have hwU := hV₁U hw
  have e3 : u * (v * u) * (w * (v * u)) = u * w := by
    calc u * (v * u) * (w * (v * u)) = u * (u * v) * (w * (u * v)) := by
          rw [hcomm v hvU u hu]
      _ = (u * u) * ((v * w) * (u * v)) := by group
      _ = (u * u) * ((w * v) * (u * v)) := by rw [hcomm v hvU w hwU]
      _ = (u * u) * (w * (v * u) * v) := by group
      _ = (u * u) * (w * (u * v) * v) := by rw [hcomm v hvU u hu]
      _ = (u * u) * (w * u * (v * v)) := by group
      _ = w * u := by rw [hsq u hu, hsq v hvU]; group
      _ = u * w := hcomm w hwU u hu
  rw [e3] at h1
  have := (fsuV1 T V).mul_mem h1 ((fsuV1 T V).inv_mem hw)
  simpa using this

end Setting4

end CFSG.Quasithin.H13.A6
