module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FF
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GP

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem inf_centralizer_L_eq_bot (he : Step3_3_21e) (h : Hyp331 G T M L D)
    (e : Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hmod : Mod3321 T L) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hUn : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
    ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer ht) (mem_normalizer_centralizer (hTL ht))
  obtain ⟨v, hv, hv1, hvC⟩ := exists_mem_center_of_ne_bot h.sylow.1 inf_le_left hUn hne
  set X : Subgroup G := T ⊓ Subgroup.centralizer (L : Set G) ⊓
    Subgroup.centralizer (T : Set G) with hX
  have hvX : v ∈ X := ⟨hv, hvC⟩
  have hX2 : IsPGroup 2 X := h.sylow.1.to_le (inf_le_left.trans inf_le_left)
  have hXne : X ≠ ⊥ := fun hb => hv1 (by rw [hb] at hvX; exact hvX)
  have hdvd : 2 ∣ Nat.card ↥X := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hXne
      rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq X hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hw2 : (w : G) ^ 2 = 1 := by
    have h1 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    simpa using congrArg Subtype.val h1
  have hw1 : (w : G) ≠ 1 := by
    intro h1
    have h2 : w = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hw
    exact absurd hw (by norm_num)
  have hwZ : (w : G) ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨w.2.1.1, w.2.2⟩, hw2⟩
  have h1 : (w : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hwZ, w.2.1.2⟩
  rw [he G T M L D h e hmod, Subgroup.mem_bot] at h1
  exact hw1 h1

theorem exists_decomp (h7 : Stmt3_3_7) (h14 : Stmt3_3_14) {α : ↥L →* SL4}
    (hD : FData G T M L D α) {t : G} (ht : t ∈ T) :
    ∃ s ∈ T ⊓ L, s⁻¹ * t ∈ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨hML, -⟩ := h14 G T M L D hD.hyp
  obtain ⟨y, hyU, hy⟩ := hD.exists_conj ht
  have hyU' := hyU
  rw [← hD.mapU] at hyU'
  obtain ⟨s, hs, hse⟩ := hyU'
  have hs' : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 hs
  set c : G := (s : G)⁻¹ * t with hc
  have hcT : c ∈ T := T.mul_mem (T.inv_mem hs'.1) ht
  have hcL : ∀ l : ↥L, ∃ k : ↥L, α k = 1 ∧ c * (l : G) * c⁻¹ = k * l := by
    intro l
    have hx : t * (l : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hD.TL ht) l).mp l.2
    let m : ↥L := s⁻¹ * ⟨t * l * t⁻¹, hx⟩ * s
    have hm : (m : G) = c * l * c⁻¹ := by
      show (s : G)⁻¹ * (t * l * t⁻¹) * s = c * l * c⁻¹
      rw [hc]
      group
    refine ⟨m * l⁻¹, ?_, by rw [Subgroup.coe_mul, Subgroup.coe_inv, hm]; group⟩
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hy l hx, hse]
    group
  have hcV : c ∈ Subgroup.centralizer (vPlus L T : Set G) := by
    have hle : vPlus L T ≤ Subgroup.centralizer ({c} : Set G) := by
      refine (vPlus_le_conjClosure hML).trans (conjClosure_le fun l hl z hz => ?_)
      obtain ⟨k, hk1, hk⟩ := hcL ⟨l, hl⟩
      have hkV : (k : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := (hD.kerV k).1 hk1
      have hlz : l * z * l⁻¹ ∈ vPlus L T := by
        show l * z * l⁻¹ ∈ conjClosure (quasithinOmegaOneCenter T) (mPlus L T)
        rw [hML]
        exact Subgroup.subset_closure ⟨l, hl, z, hz, rfl⟩
      have hcz := conj_omegaOneCenter hcT hz
      have h1 : c * (l * z * l⁻¹) * c⁻¹ = l * z * l⁻¹ := by
        have e1 : c * (l * z * l⁻¹) * c⁻¹ =
            (c * l * c⁻¹) * (c * z * c⁻¹) * (c * l * c⁻¹)⁻¹ := by group
        rw [e1, hcz, hk]
        have h2 := Subgroup.mem_centralizer_iff.1 hkV _ hlz
        calc (k : G) * l * z * ((k : G) * l)⁻¹ = ((k : G) * (l * z * l⁻¹)) * (k : G)⁻¹ := by
              group
          _ = ((l * z * l⁻¹) * k) * (k : G)⁻¹ := by rw [← h2]
          _ = l * z * l⁻¹ := by group
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc l * z * l⁻¹ * c = (c * (l * z * l⁻¹) * c⁻¹) * c := by rw [h1]
        _ = c * (l * z * l⁻¹) := by group
    exact Subgroup.mem_centralizer_iff.2 fun v hv =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hle hv))
  obtain ⟨⟨-, hCT⟩, -⟩ := h7 G T M L D hD.hyp
  rw [hML] at hCT
  refine ⟨s, hs', ?_⟩
  rw [← hCT]
  exact ⟨hcT, hcV⟩

theorem pCoreOf_LT_le (h : Hyp331 G T M L D) : pCoreOf 2 (L ⊔ T) ≤ T :=
  EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf

theorem pCoreOf_LT_eq (h7 : Stmt3_3_7) (h14 : Stmt3_3_14) (h : Hyp331 G T M L D) :
    T ⊓ Subgroup.centralizer (vPlus L T : Set G) = pCoreOf 2 (L ⊔ T) := by
  obtain ⟨hML, -⟩ := h14 G T M L D h
  obtain ⟨⟨-, hCT⟩, -⟩ := h7 G T M L D h
  rw [hML] at hCT
  exact hCT

theorem comm_mem_pCoreOf (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) {l : G} (hl : l ∈ L) :
    q * l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply inf_le_pCoreOf (T := T)
  refine ⟨?_, L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL (pCoreOf_LT_le h hq)) l).mp hl)
    (L.inv_mem hl)⟩
  have h1 : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
      (Subgroup.mem_sup_left hl)) q⁻¹).mp (Subgroup.inv_mem _ hq)
  rw [show q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) by group]
  exact Subgroup.mul_mem _ hq h1

theorem comm_mem_vPlus (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hcommL : ⁅pCoreOf 2 L, L⁆ ≤ vPlus L T) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) :
    ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T := by
  set P := pCoreOf 2 L with hP
  set V := vPlus L T with hV
  have hPL : P ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := L3317.le_normalizer_vPlus h
  have hA : ∀ x ∈ P, ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ V := by
    intro x hx l hl
    have h1 : ⁅x, l⁆ ∈ V := hcommL (Subgroup.commutator_mem_commutator hx hl)
    have h2 : l * x * l⁻¹ * x⁻¹ = ⁅x, l⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact V.inv_mem h1
  let S : Subgroup G :=
    { carrier := {l | l ∈ L ∧ q * l * q⁻¹ * l⁻¹ ∈ V}
      one_mem' := ⟨L.one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨L.mul_mem ha.1 hb.1, ?_⟩
        have e1 : q * (a * b) * q⁻¹ * (a * b)⁻¹ =
            (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e1]
        exact V.mul_mem ha.2 ((Subgroup.mem_normalizer_iff.mp (hLV ha.1) _).mp hb.2)
      inv_mem' := fun {a} ha => by
        refine ⟨L.inv_mem ha.1, ?_⟩
        have e1 : q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e1]
        exact (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem ha.1)) _).mp (V.inv_mem ha.2) }
  have hc : ∀ a ∈ L, ∀ b ∈ L, ⁅a, b⁆ ∈ S := by
    intro a ha b hb
    have hcP : ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ P := fun l hl => comm_mem_pCoreOf h hTL hq hl
    have hxP := hcP a ha
    have hyP := hcP b hb
    set x := q * a * q⁻¹ * a⁻¹ with hx
    set y := q * b * q⁻¹ * b⁻¹ with hy
    refine ⟨by rw [← hperf]; exact Subgroup.commutator_mem_commutator ha hb, ?_⟩
    set g := a * b * a⁻¹ with hg
    set k := a * b * a⁻¹ * b⁻¹ with hk
    have hgL : g ∈ L := L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)
    have hkL : k ∈ L := L.mul_mem hgL (L.inv_mem hb)
    have e1 : q * ⁅a, b⁆ * q⁻¹ * ⁅a, b⁆⁻¹ =
        x * (a * y * a⁻¹) * (g * x * g⁻¹)⁻¹ * (k * y * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      simp only [hx, hy, hg, hk]
      group
    rw [e1]
    have hPV : P ≤ Subgroup.normalizer (V : Set G) := hPL.trans hLV
    have hv1 := hA y hyP a ha
    have hv2 := hA x hxP g hgL
    have hv3 := hA y hyP k hkL
    have hv4 := hA y hyP x (hPL hxP)
    have e3 : x * (a * y * a⁻¹) * (g * x * g⁻¹)⁻¹ * (k * y * k⁻¹)⁻¹ =
        (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) *
          (y * (g * x * g⁻¹ * x⁻¹)⁻¹ * y⁻¹) * (k * y * k⁻¹ * y⁻¹)⁻¹ := by
      group
    rw [e3]
    refine V.mul_mem (V.mul_mem (V.mul_mem ?_ hv4) ?_) (V.inv_mem hv3)
    · exact (Subgroup.mem_normalizer_iff.mp (hPV hxP) _).mp hv1
    · exact (Subgroup.mem_normalizer_iff.mp (hPV hyP) _).mp (V.inv_mem hv2)
  have hle : ⁅L, L⁆ ≤ S := (Subgroup.commutator_le).2 hc
  rw [hperf] at hle
  intro l hl
  exact (hle hl).2

theorem sq_eq_one (h7 : Stmt3_3_7) (h14 : Stmt3_3_14) (h : Hyp331 G T M L D)
    (hCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hQV : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T)
    {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) : q ^ 2 = 1 := by
  have hqT := pCoreOf_LT_le h hq
  have hqC : q ∈ Subgroup.centralizer (vPlus L T : Set G) := by
    rw [← pCoreOf_LT_eq h7 h14 h] at hq
    exact hq.2
  have hVe := (Hyp331.vPlus_reduced h.toSetup331).2.1
  rw [sq]
  have hq2 : q * q ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨T.mul_mem hqT hqT, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    set c := q * l * q⁻¹ * l⁻¹ with hc
    have hcV : c ∈ vPlus L T := hQV q hq l hl
    have hqc : q * c * q⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.1 hqC c hcV
      rw [← this, mul_inv_cancel_right]
    have hc2 : c * c = 1 := by
      have := hVe.2 c hcV
      rwa [sq] at this
    have e1 : q * l * q⁻¹ = c * l := by rw [hc]; group
    have e2 : q * q * l * (q * q)⁻¹ = l := by
      calc q * q * l * (q * q)⁻¹ = q * (q * l * q⁻¹) * q⁻¹ := by group
        _ = q * (c * l) * q⁻¹ := by rw [e1]
        _ = (q * c * q⁻¹) * (q * l * q⁻¹) := by group
        _ = c * (c * l) := by rw [hqc, e1]
        _ = (c * c) * l := by group
        _ = l := by rw [hc2, one_mul]
    calc l * (q * q) = (q * q * l * (q * q)⁻¹) * (q * q) := by rw [e2]
      _ = q * q * l := by group
  rw [hCL, Subgroup.mem_bot] at hq2
  exact hq2

theorem isElemAbelian_pCoreOf (h7 : Stmt3_3_7) (h14 : Stmt3_3_14) (h : Hyp331 G T M L D)
    (hCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hQV : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ vPlus L T) :
    IsElemAbelian 2 (pCoreOf 2 (L ⊔ T)) := by
  have hsq := fun q (hq : q ∈ pCoreOf 2 (L ⊔ T)) => sq_eq_one h7 h14 h hCL hQV hq
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hsq⟩
  have ha := hsq a a.2
  have hb := hsq b b.2
  have hab := hsq _ (Subgroup.mul_mem _ a.2 b.2)
  rw [sq] at ha hb hab
  show (a : G) * b = b * a
  calc (a : G) * b = (a * b)⁻¹ := (eq_inv_of_mul_eq_one_left hab).trans rfl
    _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [inv_eq_of_mul_eq_one_left hb, inv_eq_of_mul_eq_one_left ha]

end CFSG.Quasithin.H13.L3321
