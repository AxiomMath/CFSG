module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSub3A
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cSub2A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

def ceSub (Q W : Subgroup D) (hW : ∀ w ∈ W, ∀ q ∈ Q, w * q = q * w) : Subgroup D where
  carrier := {n | n ∈ Q ∧ (∀ q ∈ Q, n * q * n⁻¹ * q⁻¹ ∈ W) ∧ n * n ∈ W}
  one_mem' := ⟨Q.one_mem, fun q _ => by simp, by simp⟩
  mul_mem' := by
    rintro n n' ⟨hn, hnc, hns⟩ ⟨hn', hn'c, hn's⟩
    have hcen : ∀ w ∈ W, ∀ m ∈ Q, m * w * m⁻¹ = w := fun w hw m hm => by
      rw [← hW w hw m hm]; group
    refine ⟨Q.mul_mem hn hn', fun q hq => ?_, ?_⟩
    · have e : n * n' * q * (n * n')⁻¹ * q⁻¹ =
          (n * (n' * q * n'⁻¹ * q⁻¹) * n⁻¹) * (n * q * n⁻¹ * q⁻¹) := by group
      rw [e, hcen _ (hn'c q hq) n hn]
      exact W.mul_mem (hn'c q hq) (hnc q hq)
    · have hc := hn'c n hn
      have e : n * n' * (n * n') = (n' * n * n'⁻¹ * n⁻¹) * (n * n) * (n' * n') := by
        calc n * n' * (n * n') = n * (n' * n) * n' := by group
          _ = n * ((n' * n * n'⁻¹ * n⁻¹) * n * n') * n' := by group
          _ = (n * (n' * n * n'⁻¹ * n⁻¹) * n⁻¹) * (n * n) * (n' * n') := by group
          _ = (n' * n * n'⁻¹ * n⁻¹) * (n * n) * (n' * n') := by rw [hcen _ hc n hn]
      rw [e]
      exact W.mul_mem (W.mul_mem hc hns) hn's
  inv_mem' := by
    rintro n ⟨hn, hnc, hns⟩
    have hcen : ∀ w ∈ W, ∀ m ∈ Q, m * w * m⁻¹ = w := fun w hw m hm => by
      rw [← hW w hw m hm]; group
    refine ⟨Q.inv_mem hn, fun q hq => ?_, ?_⟩
    · have hw := W.inv_mem (hnc q hq)
      have e : n⁻¹ * q * n⁻¹⁻¹ * q⁻¹ =
          n⁻¹ * ((n * q * n⁻¹ * q⁻¹)⁻¹) * n := by group
      rw [e]
      have := hcen _ hw n⁻¹ (Q.inv_mem hn)
      rw [inv_inv] at this
      rw [this]
      exact hw
    · have e : n⁻¹ * n⁻¹ = (n * n)⁻¹ := by group
      rw [e]
      exact W.inv_mem hns


section ASide

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.V_central_QA : ∀ w ∈ V, ∀ q ∈ pCoreOf 2 A, w * q = q * w :=
  fun _ hw _ hq => g.V_comm_QA hw hq

@[expose] def Gen3.ceA : Subgroup D := ceSub (pCoreOf 2 A) V g.V_central_QA

omit g in
theorem Gen3.mem_ceA_iff (g : Gen3 A B z V x a a₁ a₂) {n : D} :
    n ∈ g.ceA ↔ n ∈ pCoreOf 2 A ∧ (∀ q ∈ pCoreOf 2 A, n * q * n⁻¹ * q⁻¹ ∈ V) ∧ n * n ∈ V :=
  Iff.rfl

theorem Gen3.comm_conjSub_mem_V (hU : Nat.card (conjClosure V B) = 8) {h : D} (hh : h ∈ A) {w : D}
    (hw : w ∈ conjSub h (conjClosure V B)) {q : D} (hq : q ∈ pCoreOf 2 A) :
    w * q * w⁻¹ * q⁻¹ ∈ V := by
  have hu : h⁻¹ * w * h ∈ conjClosure V B := mem_conjSub.mp hw
  have hq' : h⁻¹ * q * h ∈ pCoreOf 2 A := by
    have := conj_mem_pCoreOf_left (A.inv_mem hh) hq
    simpa using this
  have h1 := g.hyp.commutator_mem_V_of_pCoreOf_left hU hu hq'
  have h2 := g.conj_mem_V hh h1
  have e : h * ((h⁻¹ * w * h) * (h⁻¹ * q * h) * (h⁻¹ * w * h)⁻¹ * (h⁻¹ * q * h)⁻¹) * h⁻¹ =
      w * q * w⁻¹ * q⁻¹ := by group
  rwa [e] at h2

theorem Gen3.mem_ceA_of_mem_conjSub (hU : Nat.card (conjClosure V B) = 8) {h : D} (hh : h ∈ A)
    {w : D} (hw : w ∈ conjSub h (conjClosure V B)) : w ∈ g.ceA := by
  have hu : h⁻¹ * w * h ∈ conjClosure V B := mem_conjSub.mp hw
  refine ⟨?_, fun q hq => g.comm_conjSub_mem_V hU hh hw hq, ?_⟩
  · have := conj_mem_pCoreOf_left hh (g.hyp.conjClosure_le_pCoreOf_left hu)
    have e : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
    rwa [e] at this
  · have h2 := g.hyp.abelian.2 _ hu
    rw [pow_two] at h2
    have e : w * w = h * ((h⁻¹ * w * h) * (h⁻¹ * w * h)) * h⁻¹ := by group
    rw [e, h2]
    simp

theorem Gen3.U_le_ceA (hU : Nat.card (conjClosure V B) = 8) : conjClosure V B ≤ g.ceA :=
  fun u hu => g.mem_ceA_of_mem_conjSub hU A.one_mem (mem_conjSub.mpr (by simpa using hu))

end ASide


section NASide

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {y e₁ e₂ : D} {Y : Subgroup D}
  (d : YDat A V a₁ y e₁ e₂ Y)

include g d

theorem YDat.Y_le_ceA (hU : Nat.card (conjClosure V B) = 8) (hyA : y ∈ A) :
    Y ≤ g.ceA := by
  have ha₁ : a₁ ∈ g.ceA := g.U_le_ceA hU g.a₁_mem_U
  have he₁ : e₁ ∈ g.ceA := by
    refine g.mem_ceA_of_mem_conjSub hU hyA (h := y) ?_
    rw [d.he₁]; exact mul_mem_conjSub g.a₁_mem_U
  have he₂ : e₂ ∈ g.ceA := by
    refine g.mem_ceA_of_mem_conjSub hU (A.mul_mem hyA hyA) (h := y * y) ?_
    have : e₂ = (y * y) * a₁ * (y * y)⁻¹ := by rw [d.he₂, d.he₁]; group
    rw [this]; exact mul_mem_conjSub g.a₁_mem_U
  rw [d.Y_def]
  exact sup_le (Subgroup.zpowers_le.mpr (g.ceA.mul_mem ha₁ he₁))
    (Subgroup.zpowers_le.mpr (g.ceA.mul_mem he₁ he₂))



omit [Finite D] in
theorem YDat.e₁_mem_NA : e₁ ∈ conjClosure V B ⊔ Y := by
  have h1 : a₁ ∈ conjClosure V B ⊔ Y := Subgroup.mem_sup_left g.a₁_mem_U
  have h2 : a₁ * e₁ ∈ conjClosure V B ⊔ Y := Subgroup.mem_sup_right d.c₁_mem
  simpa using (conjClosure V B ⊔ Y).mul_mem ((conjClosure V B ⊔ Y).inv_mem h1) h2

omit [Finite D] in
theorem YDat.e₂_mem_NA : e₂ ∈ conjClosure V B ⊔ Y := by
  have h1 := d.e₁_mem_NA g
  have h2 : e₁ * e₂ ∈ conjClosure V B ⊔ Y := Subgroup.mem_sup_right d.c₂_mem
  simpa using (conjClosure V B ⊔ Y).mul_mem ((conjClosure V B ⊔ Y).inv_mem h1) h2

theorem YDat.conjSub_le_NA (hU : Nat.card (conjClosure V B) = 8) (hyA : y ∈ A)
    (hy3 : orderOf y = 3) {h : D} (hh : h ∈ A) :
    conjSub h (conjClosure V B) ≤ conjClosure V B ⊔ Y := by
  have hVY : ∀ v ∈ V, v ∈ conjClosure V B ⊔ Y := fun v hv =>
    Subgroup.mem_sup_left (le_conjClosure V B hv)
  rcases g.conj_cases hyA hy3 hh with hc | hc | hc
  · rw [hc]; exact le_sup_left
  · intro w hw
    rw [hc] at hw
    by_cases hwV : w ∈ V
    · exact hVY w hwV
    · obtain ⟨v, hv, rfl⟩ := g.conj_elem hU hyA hw hwV
      rw [← d.he₁]
      exact (conjClosure V B ⊔ Y).mul_mem (d.e₁_mem_NA g) (hVY v hv)
  · intro w hw
    rw [hc] at hw
    by_cases hwV : w ∈ V
    · exact hVY w hwV
    · obtain ⟨v, hv, rfl⟩ := g.conj_elem hU (A.mul_mem hyA hyA) hw hwV
      have e : (y * y) * a₁ * (y * y)⁻¹ = e₂ := by rw [d.he₂, d.he₁]; group
      rw [e]
      exact (conjClosure V B ⊔ Y).mul_mem (d.e₂_mem_NA g) (hVY v hv)

theorem YDat.A_le_normalizer_NA (hU : Nat.card (conjClosure V B) = 8) (hyA : y ∈ A)
    (hy3 : orderOf y = 3) :
    A ≤ Subgroup.normalizer ((conjClosure V B ⊔ Y : Subgroup D) : Set D) := by
  refine le_normalizer_of_conj_mem fun h hh m hm => ?_
  have hle : conjClosure V B ⊔ Y ≤
      (conjClosure V B ⊔ Y).comap (MulAut.conj h).toMonoidHom := by
    refine sup_le (fun u hu => ?_) (fun w hw => ?_)
    · show (MulAut.conj h) u ∈ conjClosure V B ⊔ Y
      rw [MulAut.conj_apply]
      exact d.conjSub_le_NA g hU hyA hy3 hh (mul_mem_conjSub hu)
    · show (MulAut.conj h) w ∈ conjClosure V B ⊔ Y
      rw [MulAut.conj_apply]
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (d.norm hh) w).mp hw)
  exact hle hm

theorem YDat.inf_Y_eq (hU : Nat.card (conjClosure V B) = 8) (hyA : y ∈ A) :
    conjClosure V B ⊓ Y = V := by
  apply le_antisymm
  · rintro w ⟨hwU, hwY⟩
    rcases g.mem_U_cases hU hwU with hV | ⟨v, hv, rfl⟩
    · exact hV
    · exfalso
      have ha₁Y : a₁ ∈ Y := by
        simpa using Y.mul_mem (Y.inv_mem (d.V_le hv)) hwY
      have he₁Y : e₁ ∈ Y := by
        rw [d.he₁]
        exact (Subgroup.mem_normalizer_iff.mp (d.norm hyA) a₁).mp ha₁Y
      exact d.noncomm (d.comm a₁ ha₁Y e₁ he₁Y)
  · exact le_inf (le_conjClosure V B) d.V_le

theorem YDat.card_NA (hU : Nat.card (conjClosure V B) = 8) (hyA : y ∈ A) :
    Nat.card ↥(conjClosure V B ⊔ Y) = 32 := by
  have hn : conjClosure V B ≤ Subgroup.normalizer (Y : Set D) :=
    (g.hyp.conjClosure_le_pCoreOf_left.trans (pCoreOf_le 2 A)).trans d.norm
  have h1 := card_sup_mul_card_inf_of_le_normalizer hn
  rw [d.inf_Y_eq g hU hyA, g.hyp.natural.card_eq, hU, d.card] at h1
  omega

theorem YDat.NA_le_QA : conjClosure V B ⊔ Y ≤ pCoreOf 2 A :=
  sup_le g.hyp.conjClosure_le_pCoreOf_left d.Y_le

theorem YDat.NA_le_ceA (hU : Nat.card (conjClosure V B) = 8) (hyA : y ∈ A) :
    conjClosure V B ⊔ Y ≤ g.ceA :=
  sup_le (g.U_le_ceA hU) (d.Y_le_ceA g hU hyA)

end NASide

section Chi

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

@[expose] def Gen3.chi (hU : Nat.card (conjClosure V B) = 8) : ↥(pCoreOf 2 A) →* D :=
  MonoidHom.mk' (fun q => a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹) (by
    intro p q
    have hcb := g.hyp.commutator_mem_V_of_pCoreOf_left hU g.a₁_mem_U q.2
    have hcom : (a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹) * (p : D) =
        (p : D) * (a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹) := g.V_comm_QA hcb p.2
    simp only [Subgroup.coe_mul]
    calc a₁ * ((p : D) * (q : D)) * a₁⁻¹ * ((p : D) * (q : D))⁻¹
        = (a₁ * (p : D) * a₁⁻¹ * (p : D)⁻¹) *
          ((p : D) * (a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹) * (p : D)⁻¹) := by group
      _ = _ := by rw [← hcom]; group)

theorem Gen3.chi_apply (hU : Nat.card (conjClosure V B) = 8) (q : ↥(pCoreOf 2 A)) :
    g.chi hU q = a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹ := rfl

theorem Gen3.chi_mem_V (hU : Nat.card (conjClosure V B) = 8) (q : ↥(pCoreOf 2 A)) :
    g.chi hU q ∈ V :=
  g.hyp.commutator_mem_V_of_pCoreOf_left hU g.a₁_mem_U q.2

theorem Gen3.chi_eq_one_iff (hU : Nat.card (conjClosure V B) = 8) (q : ↥(pCoreOf 2 A)) :
    g.chi hU q = 1 ↔ (q : D) ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  constructor
  · intro h1
    have hqB : (q : D) ∈ B := (g.hyp.gold.pCoreOf_left_le q.2).2
    have hc : a₁ * (q : D) = (q : D) * a₁ := by
      calc a₁ * (q : D) = (a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹) * ((q : D) * a₁) := by group
        _ = (q : D) * a₁ := by rw [show a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹ = 1 from h1, one_mul]
    exact g.hyp.mem_coreIn_of_comm q.2
      (fun u hu => g.comm_U_of hU hqB (g.V_comm_QA g.a_mem q.2) hc hu)
  · intro hq
    have hc : a₁ * (q : D) = (q : D) * a₁ := g.hyp.comm_of_mem_coreIn hq a₁ g.a₁_mem_U
    show a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹ = 1
    rw [hc]; group

end Chi


section KSide

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {y e₁ e₂ : D} {Y : Subgroup D}
  (d : YDat A V a₁ y e₁ e₂ Y)

include g d

theorem YDat.chi_e₁ (hU : Nat.card (conjClosure V B) = 8) :
    g.chi hU ⟨e₁, d.e₁_mem⟩ = a₁ * e₁ * a₁ * e₁ := by
  rw [g.chi_apply]
  have h1 : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right g.a₁_sq
  have h2 : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right d.e₁_sq
  show a₁ * e₁ * a₁⁻¹ * e₁⁻¹ = _
  rw [h1, h2]

theorem YDat.chi_e₂ (hU : Nat.card (conjClosure V B) = 8) :
    g.chi hU ⟨e₂, d.e₂_mem⟩ = a₁ * e₂ * a₁ * e₂ := by
  rw [g.chi_apply]
  have h1 : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right g.a₁_sq
  have h2 : e₂⁻¹ = e₂ := inv_eq_of_mul_eq_one_right d.e₂_sq
  show a₁ * e₂ * a₁⁻¹ * e₂⁻¹ = _
  rw [h1, h2]

theorem YDat.V_le_map_chi (hU : Nat.card (conjClosure V B) = 8) :
    V ≤ ((conjClosure V B ⊔ Y).subgroupOf (pCoreOf 2 A)).map (g.chi hU) := by
  have hκ1V : a₁ * e₁ * a₁ * e₁ ∈ V := by rw [← d.chi_e₁ g hU]; exact g.chi_mem_V hU _
  have hκ3V : a₁ * e₂ * a₁ * e₂ ∈ V := by rw [← d.chi_e₂ g hU]; exact g.chi_mem_V hU _
  have hsq : (a₁ * e₁ * a₁ * e₁) * (a₁ * e₁ * a₁ * e₁) = 1 := g.V_sq hκ1V
  have hVle := le_sup_zpowers_of_card_four g.hyp.natural.card_eq hκ1V hκ3V hsq d.κ₁_ne d.κ₃_ne
    (fun h => d.κ_ne h.symm)
  refine hVle.trans (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
  · exact ⟨⟨e₁, d.e₁_mem⟩, Subgroup.mem_subgroupOf.mpr (d.e₁_mem_NA g), d.chi_e₁ g hU⟩
  · exact ⟨⟨e₂, d.e₂_mem⟩, Subgroup.mem_subgroupOf.mpr (d.e₂_mem_NA g), d.chi_e₂ g hU⟩

theorem YDat.exists_mem_NA_mul (hU : Nat.card (conjClosure V B) = 8) {q : D}
    (hq : q ∈ pCoreOf 2 A) :
    ∃ n ∈ conjClosure V B ⊔ Y, n⁻¹ * q ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  obtain ⟨n', hn', hnq⟩ := d.V_le_map_chi g hU (g.chi_mem_V hU ⟨q, hq⟩)
  refine ⟨(n' : D), Subgroup.mem_subgroupOf.mp hn', ?_⟩
  have := (g.chi_eq_one_iff hU (n'⁻¹ * ⟨q, hq⟩)).mp (by rw [map_mul, map_inv, hnq]; group)
  simpa using this

theorem YDat.card_K (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128) :
    Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) = 16 := by
  have hker : (g.chi hU).ker =
      (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B).subgroupOf (pCoreOf 2 A) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, g.chi_eq_one_iff hU]
  have hrange : (g.chi hU).range = V := by
    apply le_antisymm
    · rintro _ ⟨q, rfl⟩
      exact g.chi_mem_V hU q
    · intro w hw
      obtain ⟨n, -, hn⟩ := d.V_le_map_chi g hU hw
      exact ⟨n, hn⟩
  have hidx : (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B).relIndex (pCoreOf 2 A) = 4 := by
    have := Subgroup.index_ker (g.chi hU)
    rw [hker, hrange, g.hyp.natural.card_eq] at this
    exact this
  have h1 := card_eq_relIndex_mul (coreIn_right_le_pCoreOf_left (A := A) (B := B))
  rw [hidx, g.card_QA' hT] at h1
  omega

theorem YDat.relIndex_U_K (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 128) :
    (conjClosure V B).relIndex (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) = 2 := by
  have h1 := card_eq_relIndex_mul g.hyp.conjClosure_le_coreIn
  rw [d.card_K g hU hT, hU] at h1
  omega

end KSide

section KSq

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.K_sq_mem (hU : Nat.card (conjClosure V B) = 8)
    (h2 : (conjClosure V B).relIndex (coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) = 2) {k : D}
    (hk : k ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) : k * k ∈ Subgroup.zpowers z := by
  set K := coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B with hK
  have hKB : K ≤ B := (coreIn_le_right _ _).trans (inf_le_right.trans (pCoreOf_le 2 B))
  have hksqU : k * k ∈ conjClosure V B := by
    have := GoldAmN.sq_mem_of_relIndex_two g.hyp.conjClosure_le_coreIn
      (fun k' hk' => le_normalizer_conjClosure V B (hKB hk')) h2 hk
    simpa [pow_two] using this
  by_cases hkU : k ∈ conjClosure V B
  · have : k * k = 1 := by
      have := g.hyp.abelian.2 k hkU
      rwa [pow_two] at this
    rw [this]
    exact Subgroup.one_mem _
  · have hxk : x * k * x⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ g.x_mem) k).mp hk
    have hxkU : x * k * x⁻¹ ∉ conjClosure V B := fun h =>
      hkU ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B g.x_mem) k).mpr h)
    have hu := mul_inv_mem_of_relIndex_two h2 hxk hk hxkU hkU
    set u := x * k * x⁻¹ * k⁻¹ with hu_def
    have hcomm : u * k = k * u := g.hyp.comm_of_mem_coreIn hk u hu
    have hxk' : x * k * x⁻¹ = u * k := by rw [hu_def]; group
    have huu : u * u = 1 := by
      have := g.hyp.abelian.2 u hu
      rwa [pow_two] at this
    have hfix : x * (k * k) * x⁻¹ = k * k := by
      calc x * (k * k) * x⁻¹ = (x * k * x⁻¹) * (x * k * x⁻¹) := by group
        _ = (u * k) * (u * k) := by rw [hxk']
        _ = u * (k * u) * k := by group
        _ = u * (u * k) * k := by rw [hcomm]
        _ = (u * u) * (k * k) := by group
        _ = k * k := by rw [huu, one_mul]
    have h4 : k * k ∈ conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D) := by
      refine ⟨hksqU, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc y * (k * k) = (y * (k * k) * y⁻¹) * y := by group
        _ = (k * k) * y := by rw [hfix]
    rw [g.U_inf_centralizer_x hU] at h4
    exact h4

end KSq

section SqQA

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂) {y e₁ e₂ : D} {Y : Subgroup D}
  (d : YDat A V a₁ y e₁ e₂ Y)

include g d

theorem YDat.sq_mem_V_QA (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 128)
    (hyA : y ∈ A) {q : D} (hq : q ∈ pCoreOf 2 A) : q * q ∈ V := by
  obtain ⟨n, hn, hk⟩ := d.exists_mem_NA_mul g hU hq
  set k := n⁻¹ * q with hkdef
  have hq' : q = n * k := by rw [hkdef]; group
  obtain ⟨hnQ, hnc', hns⟩ := d.NA_le_ceA g hU hyA hn
  have hkQ : k ∈ pCoreOf 2 A := coreIn_right_le_pCoreOf_left hk
  have hksq := g.K_sq_mem hU (d.relIndex_U_K g hU hT) hk
  have hc : n * k * n⁻¹ * k⁻¹ ∈ V := hnc' k hkQ
  have hc' : k * n * k⁻¹ * n⁻¹ ∈ V := by
    have := V.inv_mem hc
    have e : (n * k * n⁻¹ * k⁻¹)⁻¹ = k * n * k⁻¹ * n⁻¹ := by group
    rwa [e] at this
  have hcen : n * (k * n * k⁻¹ * n⁻¹) = (k * n * k⁻¹ * n⁻¹) * n :=
    (g.V_comm_QA hc' hnQ).symm
  have e : q * q = (k * n * k⁻¹ * n⁻¹) * (n * n) * (k * k) := by
    rw [hq']
    calc n * k * (n * k) = n * (k * n * k⁻¹ * n⁻¹) * n * (k * k) := by group
      _ = (k * n * k⁻¹ * n⁻¹) * n * n * (k * k) := by rw [hcen]
      _ = _ := by group
  rw [e]
  have hzV : k * k ∈ V := (Subgroup.zpowers_le.mpr g.hyp.natural.z_mem_V) hksq
  exact V.mul_mem (V.mul_mem hc' hns) hzV

end SqQA

end GoldAmL3c

end F6

end CFSG.Quasithin
