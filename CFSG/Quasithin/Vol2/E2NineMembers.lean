module

public import CFSG.Quasithin.Vol2.E2StatementsAS
public import CFSG.Quasithin.Background.E2Pair
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

omit [Finite G] in
private theorem mem_normalizer_sup {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem commutator_mem_pCoreOf (h : Hyp28 H T M V) {v j : G} (hv : v ∈ V)
    (hj : j ∈ kerIn M H) : v * j * v⁻¹ * j⁻¹ ∈ pCoreOf 2 H := by
  have hmp := h.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  have hvM : v ∈ pCoreOf 2 M := h.le_pCoreOf hv
  have hvM' : v ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hvM
  have hjM : j ∈ M := kerIn_le hj
  have h1 : v * j * v⁻¹ * j⁻¹ ∈ kerIn M H := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M H (hMH hvM')) j).mp hj
    exact (kerIn M H).mul_mem this ((kerIn M H).inv_mem hj)
  have h2 : v * j * v⁻¹ * j⁻¹ ∈ pCoreOf 2 M := by
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hjM) v⁻¹).mp ((pCoreOf 2 M).inv_mem hvM)
    have e : v * j * v⁻¹ * j⁻¹ = v * (j * v⁻¹ * j⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 M).mul_mem hvM this
  have hle : pCoreOf 2 M ⊓ kerIn M H ≤ pCoreOf 2 H :=
    hmp.le_pCoreOf_of_isPGroup_of_le_kerIn
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left) inf_le_right
  exact hle ⟨h2, h1⟩

def centModP (H M : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ H ∧ ∀ j ∈ kerIn M H, x * j * x⁻¹ * j⁻¹ ∈ pCoreOf 2 H}
  one_mem' := ⟨H.one_mem, fun j _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxj⟩ ⟨hy, hyj⟩
    refine ⟨H.mul_mem hx hy, fun j hj => ?_⟩
    have e : x * y * j * (x * y)⁻¹ * j⁻¹ =
        x * (y * j * y⁻¹ * j⁻¹) * x⁻¹ * (x * j * x⁻¹ * j⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hx) _).mp (hyj j hj)) (hxj j hj)
  inv_mem' := by
    rintro x ⟨hx, hxj⟩
    refine ⟨H.inv_mem hx, fun j hj => ?_⟩
    have e : x⁻¹ * j * x⁻¹⁻¹ * j⁻¹ = x⁻¹ * (x * j * x⁻¹ * j⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hx)) _).mp
      ((pCoreOf 2 H).inv_mem (hxj j hj))

theorem commutator_kerIn_le (h : Hyp28 H T M V) {g : G} (hg : g ∈ H) :
    ⁅kerIn M H, V ⊔ B6.conjSub g V⁆ ≤ pCoreOf 2 H := by
  have hVC : V ≤ centModP H M := fun v hv => ⟨h.le_H hv, fun j hj =>
    commutator_mem_pCoreOf h hv hj⟩
  have hWC : B6.conjSub g V ≤ centModP H M := by
    intro w hw
    rw [B6.mem_conjSub] at hw
    have hwH : w ∈ H := by
      have := H.mul_mem (H.mul_mem hg (h.le_H hw)) (H.inv_mem hg)
      simpa [mul_assoc] using this
    refine ⟨hwH, fun j hj => ?_⟩
    have hj' : g⁻¹ * j * g ∈ kerIn M H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M H (H.inv_mem hg)) j).mp hj
      simpa using this
    have hc := commutator_mem_pCoreOf h hw hj'
    have e : w * j * w⁻¹ * j⁻¹ =
        g * ((g⁻¹ * w * g) * (g⁻¹ * j * g) * (g⁻¹ * w * g)⁻¹ * (g⁻¹ * j * g)⁻¹) * g⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) _).mp hc
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro x hx j hj
  exact (sup_le hVC hWC hx).2 j hj

theorem pCoreOf_le_normalizer (h : Hyp28 H T M V) {g : G} (hg : g ∈ H) :
    pCoreOf 2 H ≤ Subgroup.normalizer ((V ⊔ B6.conjSub g V : Subgroup G) : Set G) := by
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.minParabolic.isSylow
  intro q hq
  refine mem_normalizer_sup (h.normal_T (hQT hq)) ?_
  have hq' : g⁻¹ * q * g ∈ pCoreOf 2 H := by
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hg)) q).mp hq
    simpa using this
  have hn := h.normal_T (hQT hq')
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro w
  rw [B6.mem_conjSub, B6.mem_conjSub]
  have e : g⁻¹ * (q * w * q⁻¹) * g =
      (g⁻¹ * q * g) * (g⁻¹ * w * g) * (g⁻¹ * q * g)⁻¹ := by group
  rw [e]
  exact hn _

theorem kerIn_le_normalizer_oTwoUpper (h : Hyp28 H T M V) {g : G} (hg : g ∈ H) :
    kerIn M H ≤ Subgroup.normalizer
      ((oTwoUpper (V ⊔ B6.conjSub g V) : Subgroup G) : Set G) := by
  set I := V ⊔ B6.conjSub g V with hIdef
  have hIH : I ≤ H := sup_le h.le_H (by
    intro w hw
    rw [B6.mem_conjSub] at hw
    have := H.mul_mem (H.mul_mem hg (h.le_H hw)) (H.inv_mem hg)
    simpa [mul_assoc] using this)
  have hcomm := commutator_kerIn_le h hg
  have hQN := pCoreOf_le_normalizer h hg
  have key : ∀ j ∈ kerIn M H, ∀ x ∈ I, Odd (orderOf x) → j * x * j⁻¹ ∈ I := by
    intro j hj x hx hodd
    set X := pCoreOf 2 H ⊔ I with hX
    have hIX : I ≤ X := le_sup_right
    have hIn : (I.subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hIX]
      exact sup_le hQN Subgroup.le_normalizer
    have hc : j * x * j⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
      have h1 := hcomm (Subgroup.commutator_mem_commutator hj hx)
      rw [commutatorElement_def] at h1
      exact h1
    have hyX : j * x * j⁻¹ ∈ X := by
      have e : j * x * j⁻¹ = (j * x * j⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact X.mul_mem (le_sup_left (a := pCoreOf 2 H) hc) (hIX hx)
    set φ := QuotientGroup.mk' (I.subgroupOf X)
    have hcX : j * x * j⁻¹ * x⁻¹ ∈ X := le_sup_left (a := pCoreOf 2 H) hc
    have himg : φ ⟨j * x * j⁻¹, hyX⟩ = φ ⟨j * x * j⁻¹ * x⁻¹, hcX⟩ := by
      have e : (⟨j * x * j⁻¹, hyX⟩ : X) = ⟨j * x * j⁻¹ * x⁻¹, hcX⟩ * ⟨x, hIX hx⟩ :=
        Subtype.ext (by simp)
      have hx1 : φ ⟨x, hIX hx⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hx
      rw [e, map_mul, hx1, mul_one]
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hc⟩
    have hk' : (⟨j * x * j⁻¹ * x⁻¹, hcX⟩ : X) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf (φ ⟨j * x * j⁻¹, hyX⟩) ∣ 2 ^ k := by
      rw [himg]
      exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
    have hconj : orderOf (j * x * j⁻¹) = orderOf x := by
      have := orderOf_injective (MulAut.conj j).toMonoidHom (MulAut.conj j).injective x
      simpa [MulAut.conj_apply] using this
    have hodd' : Odd (orderOf (⟨j * x * j⁻¹, hyX⟩ : X)) := by
      rw [Subgroup.orderOf_mk, hconj]
      exact hodd
    have h3 : orderOf (φ ⟨j * x * j⁻¹, hyX⟩) ∣ orderOf (⟨j * x * j⁻¹, hyX⟩ : X) :=
      orderOf_map_dvd _ _
    have h1 : orderOf (φ ⟨j * x * j⁻¹, hyX⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k
        (Nat.coprime_two_right.2 (hodd'.of_dvd_nat h3))) h2
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  have hsub : ∀ j ∈ kerIn M H, (oTwoUpper I).map (MulAut.conj j).toMonoidHom ≤ oTwoUpper I := by
    intro j hj
    rw [oTwoUpper, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hx, hodd⟩, rfl⟩
    refine Subgroup.subset_closure ⟨key j hj x hx hodd, ?_⟩
    have := orderOf_injective (MulAut.conj j).toMonoidHom (MulAut.conj j).injective x
    rw [this]
    exact hodd
  intro j hj
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hsub j hj) ?_
  have h1 := Subgroup.map_mono (f := (MulAut.conj j).toMonoidHom)
    (hsub j⁻¹ ((kerIn M H).inv_mem hj))
  rwa [Subgroup.map_map, show (MulAut.conj j).toMonoidHom.comp (MulAut.conj j⁻¹).toMonoidHom =
    MonoidHom.id G from MonoidHom.ext fun y => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group, Subgroup.map_id] at h1

theorem charTwo_of_charTwo (h : Hyp28 H T M V) {g : G} (hg : g ∈ H) (hchar : CharTwo H) :
    CharTwo (V ⊔ B6.conjSub g V) := by
  set I := V ⊔ B6.conjSub g V with hIdef
  have hIH : I ≤ H := sup_le h.le_H (by
    intro w hw
    rw [B6.mem_conjSub] at hw
    have := H.mul_mem (H.mul_mem hg (h.le_H hw)) (H.inv_mem hg)
    simpa [mul_assoc] using this)
  have hQN := pCoreOf_le_normalizer h hg
  set Q := pCoreOf 2 H with hQdef
  set R := pCoreOf 2 I with hRdef
  set C := I ⊓ Subgroup.centralizer (R : Set G) with hCdef
  have hNR : Subgroup.normalizer (I : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 I
  have hNC : ∀ x ∈ Subgroup.normalizer (I : Set G), x ∈ Subgroup.normalizer (C : Set G) := by
    intro x hx
    have hxR := hNR hx
    rw [Subgroup.mem_normalizer_iff] at hx hxR ⊢
    intro c
    constructor
    · rintro ⟨hcI, hcR⟩
      refine ⟨(hx c).1 hcI, ?_⟩
      replace hcR : c ∈ Subgroup.centralizer (R : Set G) := hcR
      show x * c * x⁻¹ ∈ Subgroup.centralizer (R : Set G)
      rw [Subgroup.mem_centralizer_iff] at hcR ⊢
      intro r hr
      have hr' : x⁻¹ * r * x ∈ R := by
        have := hxR (x⁻¹ * r * x)
        have e : x * (x⁻¹ * r * x) * x⁻¹ = r := by group
        rw [e] at this
        exact this.mpr hr
      have := hcR _ hr'
      calc r * (x * c * x⁻¹) = x * ((x⁻¹ * r * x) * c) * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * r * x)) * x⁻¹ := by rw [this]
        _ = x * c * x⁻¹ * r := by group
    · rintro ⟨hcI, hcR⟩
      refine ⟨(hx c).2 hcI, ?_⟩
      replace hcR : x * c * x⁻¹ ∈ Subgroup.centralizer (R : Set G) := hcR
      show c ∈ Subgroup.centralizer (R : Set G)
      rw [Subgroup.mem_centralizer_iff] at hcR ⊢
      intro r hr
      have hr' : x * r * x⁻¹ ∈ R := (hxR r).1 hr
      have := hcR _ hr'
      have e1 : r * c = x⁻¹ * ((x * r * x⁻¹) * (x * c * x⁻¹)) * x := by group
      have e2 : c * r = x⁻¹ * ((x * c * x⁻¹) * (x * r * x⁻¹)) * x := by group
      rw [e1, e2, this]
  have hCQR : C ⊓ Q ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans inf_le_left)
      ?_ ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
    intro x hx
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hIH hx)
    have hxC := hNC x (Subgroup.le_normalizer hx)
    rw [Subgroup.mem_normalizer_iff] at hxQ hxC ⊢
    intro y
    exact ⟨fun ⟨h1, h2⟩ => ⟨(hxC y).1 h1, (hxQ y).1 h2⟩,
      fun ⟨h1, h2⟩ => ⟨(hxC y).2 h1, (hxQ y).2 h2⟩⟩
  have hodd1 : ∀ b ∈ C, Odd (orderOf b) → b = 1 := by
    intro b hb hodd
    have hbQ : b ∈ H ⊓ Subgroup.centralizer (Q : Set G) := by
      refine ⟨hIH hb.1, ?_⟩
      show b ∈ Subgroup.centralizer (Q : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqN := hQN hq
      have hd : b * q * b⁻¹ * q⁻¹ ∈ C ⊓ Q := by
        constructor
        · have hqC := hNC q hqN
          have h1 : q * b⁻¹ * q⁻¹ ∈ C :=
            (Subgroup.mem_normalizer_iff.mp hqC b⁻¹).mp (C.inv_mem hb)
          have e : b * q * b⁻¹ * q⁻¹ = b * (q * b⁻¹ * q⁻¹) := by group
          rw [e]
          exact C.mul_mem hb h1
        · have h1 : b * q * b⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp
              (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hIH hb.1)) q).mp hq
          exact Q.mul_mem h1 (Q.inv_mem hq)
      have hdR := hCQR hd
      have hcomm : b * (b * q * b⁻¹ * q⁻¹) = (b * q * b⁻¹ * q⁻¹) * b :=
        (Subgroup.mem_centralizer_iff.mp hb.2 _ hdR).symm
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hd.2⟩
      have hk' : (b * q * b⁻¹ * q⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact (commute_of_odd_of_commutator hodd hcomm ⟨k, hk'⟩).symm
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨b, hchar hbQ⟩
    exact eq_one_of_odd_orderOf_of_pow_two_pow hodd (by simpa using congrArg Subtype.val hk)
  have hC2 : IsPGroup 2 C := by
    rintro ⟨c, hc⟩
    obtain ⟨a, b, hcab, ha, hb, ⟨k, hk⟩, hbodd⟩ := exists_two_part_odd_part c
    have hbC : b ∈ C := (Subgroup.zpowers_le.mpr hc) hb
    have hca : c = a := by rw [hcab, hodd1 b hbC hbodd, one_mul]
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [hca]
    exact hk
  intro x hx
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun y hy => hNC y (Subgroup.le_normalizer hy)) hC2 hx

end E2

theorem ASInputs.e2_9C_members {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}
    (h : E2.Hyp28 H T M V) {I : Subgroup G} (hI : ASInputs.IsInIHTVC H T M V I) :
    (⁅kerIn M H, I⁆ ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ Subgroup.normalizer (I : Set G) ∧
        kerIn M H ≤ Subgroup.normalizer (oTwoUpper I : Set G)) ∧
      (CharTwo H → CharTwo I) := by
  obtain ⟨hIH, ⟨g, hgI, rfl⟩, -⟩ := hI
  have hg : g ∈ H := hIH hgI
  exact ⟨⟨E2.commutator_kerIn_le h hg, E2.pCoreOf_le_normalizer h hg,
    E2.kerIn_le_normalizer_oTwoUpper h hg⟩, E2.charTwo_of_charTwo h hg⟩

end CFSG.Quasithin
