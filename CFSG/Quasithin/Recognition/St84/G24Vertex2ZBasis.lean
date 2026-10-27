module

public import CFSG.GroupTheory.PGroup.ClassTwoCoordinates
import CFSG.Quasithin.Recognition.St84.G24Tools
public import CFSG.Quasithin.Background.HSL4Q13
public import CFSG.Quasithin.Recognition.St84.G24Vertex2Frame

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7 CFSG.Quasithin.St84
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective EBasis
  conj_eElt map_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem eElt_add_mul_inv_mem conj_eElt_mul_inv_mem
  conj_eElt_eq_mulVec eElt_eElt_eq_eElt_mulVec toAdd_eElt)
open Certificates.A5GL42 (aN bN)
open CFSG.Quasithin.H.Q13 (om)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

@[expose] def G24Frame2.IsZBasis (F : G24Frame2 L1 L2 S) (zb : Fin 4 → G) : Prop :=
  (∀ t, zb t ∈ centerOf (dsQ L2 L1 S)) ∧ (∀ u, eElt zb u = 1 → u = 0) ∧
    (∀ t, F.a * zb t * F.a⁻¹ = eElt zb fun s => aN s t) ∧
    (∀ t, F.b * zb t * F.b⁻¹ = eElt zb fun s => bN s t) ∧
    ∀ t, F.k * zb t * F.k⁻¹ = zb t

@[expose] def G24Frame2.IsAct (F : G24Frame2 L1 L2 S) (u : G) (n : Fin 4 → G)
    (X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)) : Prop :=
  (∀ j, F.a * v2Frame F.k u n j * F.a⁻¹ *
      (eElt (v2Frame F.k u n) fun i => v2Block 1 (X 0) aN i j)⁻¹ ∈ centerOf (dsQ L2 L1 S)) ∧
  (∀ j, F.b * v2Frame F.k u n j * F.b⁻¹ *
      (eElt (v2Frame F.k u n) fun i => v2Block 1 (X 1) bN i j)⁻¹ ∈ centerOf (dsQ L2 L1 S)) ∧
  ∀ j, F.k * v2Frame F.k u n j * F.k⁻¹ *
      (eElt (v2Frame F.k u n) fun i => v2Block om (X 2) F.Mk i j)⁻¹ ∈
        centerOf (dsQ L2 L1 S)

theorem G24Vertex2.toAdd_phi_eElt_gen {n d : ℕ} {Z : Subgroup G}
    (φ : ↥Z →* Multiplicative (Fin d → ZMod 2)) (z : Fin n → G)
    (hz : ∀ t, z t ∈ Z) (w : Fin n → Fin d → ZMod 2)
    (hφ : ∀ t, Multiplicative.toAdd (φ ⟨z t, hz t⟩) = w t) (u : Fin n → ZMod 2) :
    Multiplicative.toAdd (φ ⟨eElt z u, eElt_mem_of_forall_mem hz u⟩) =
      ∑ t, (u t).val • w t := by
  classical
  set zZ : Fin n → ↥Z := fun t => ⟨z t, hz t⟩ with hzZ
  have hcoe : (⟨eElt z u, eElt_mem_of_forall_mem hz u⟩ : ↥Z) = eElt zZ u := by
    apply Subtype.ext
    simp only [eElt, List.ofFn_eq_map]
    rw [SubmonoidClass.coe_list_prod, List.map_map]
    congr 1
  rw [hcoe, map_eElt φ u, toAdd_eElt]
  congr 1
  funext t
  rw [hφ t]

theorem G24Vertex2.toAdd_phi_eElt {d : ℕ} {Z : Subgroup G}
    (φ : ↥Z →* Multiplicative (Fin d → ZMod 2)) (z : Fin d → G)
    (hz : ∀ t, z t ∈ Z) (hφ : ∀ t, φ ⟨z t, hz t⟩ = Multiplicative.ofAdd (Pi.single t 1))
    (u : Fin d → ZMod 2) :
    Multiplicative.toAdd (φ ⟨eElt z u, eElt_mem_of_forall_mem hz u⟩) = u := by
  rw [G24Vertex2.toAdd_phi_eElt_gen φ z hz (fun t => Pi.single t 1) (fun t => by rw [hφ t]; rfl) u]
  have hsum : (∑ t : Fin d, (u t).val • (Pi.single t (1 : ZMod 2) : Fin d → ZMod 2)) = u := by
    funext s
    rw [Finset.sum_apply, Finset.sum_eq_single s]
    · simp [Pi.single_eq_same]
    · intro t _ hts
      simp [Pi.single_eq_of_ne (Ne.symm hts)]
    · intro hs
      simp at hs
  exact hsum

theorem G24Frame2.exists_zBasis [Finite G] (F : G24Frame2 L1 L2 S) :
    ∃ zb, F.IsZBasis zb := by
  classical
  choose zb hzb using fun t =>
    F.FZ.surj (Multiplicative.ofAdd (Pi.single t (1 : ZMod 2)))
  let z : Fin 4 → G := fun t => (zb t : G)
  have hzZ : ∀ t, z t ∈ centerOf (dsQ L2 L1 S) := fun t => (zb t).2
  have hφ : ∀ t, F.FZ.φ ⟨z t, hzZ t⟩ =
      Multiplicative.ofAdd (Pi.single t (1 : ZMod 2)) := fun t => hzb t
  have hFZinj : Function.Injective F.FZ.φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hk := (F.FZ.ker y).mp hy
    exact Subtype.ext (Subgroup.mem_bot.mp hk)
  have hind : ∀ u, eElt z u = 1 → u = 0 := by
    intro u hu
    have h0 : Multiplicative.toAdd (F.FZ.φ ⟨eElt z u, eElt_mem_of_forall_mem hzZ u⟩) = 0 := by
      rw [show (⟨eElt z u, eElt_mem_of_forall_mem hzZ u⟩ : ↥(centerOf (dsQ L2 L1 S))) = 1 from
        Subtype.ext hu, map_one]
      rfl
    have h1 := G24Vertex2.toAdd_phi_eElt F.FZ.φ z hzZ hφ u
    rw [h1] at h0
    exact h0
  have hZ2N : L2 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (centerOf (dsQ L2 L1 S) : Set G) :=
    P_le_normalizer_centerOf_dsQ_right L1 L2 S
  have hact : ∀ t, F.a * z t * F.a⁻¹ = eElt z (fun s => aN s t) := by
    intro t
    let aP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨F.a, (F.A_le F.a_mem.1).1⟩
    let zP : ↥(centerOf (dsQ L2 L1 S)) := ⟨z t, hzZ t⟩
    let e : ↥(centerOf (dsQ L2 L1 S)) := conjE hZ2N aP zP
    have hactv := F.FZ.act aP zP e (coe_conjE hZ2N aP zP)
    have hφa : Multiplicative.toAdd (F.FZ.φ e) = fun s => aN s t := by
      rw [← hactv, hφ t, F.FZ_a aP rfl]
      exact Matrix.mulVec_single_one aN t
    have hcolu : Multiplicative.toAdd (F.FZ.φ e) =
        Multiplicative.toAdd (F.FZ.φ ⟨eElt z (fun s => aN s t),
          eElt_mem_of_forall_mem hzZ _⟩) := by
      rw [hφa, G24Vertex2.toAdd_phi_eElt F.FZ.φ z hzZ hφ]
    have heq : e = ⟨eElt z (fun s => aN s t), eElt_mem_of_forall_mem hzZ _⟩ :=
      hFZinj (Multiplicative.toAdd.injective hcolu)
    calc F.a * z t * F.a⁻¹ = (e : G) := (coe_conjE hZ2N aP zP).symm
      _ = eElt z (fun s => aN s t) := by rw [heq]
  have hbct : ∀ t, F.b * z t * F.b⁻¹ = eElt z (fun s => bN s t) := by
    intro t
    let bP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨F.b, (F.A_le F.b_mem.1).1⟩
    let zP : ↥(centerOf (dsQ L2 L1 S)) := ⟨z t, hzZ t⟩
    let e : ↥(centerOf (dsQ L2 L1 S)) := conjE hZ2N bP zP
    have hactv := F.FZ.act bP zP e (coe_conjE hZ2N bP zP)
    have hφa : Multiplicative.toAdd (F.FZ.φ e) = fun s => bN s t := by
      rw [← hactv, hφ t, F.FZ_b bP rfl]
      exact Matrix.mulVec_single_one bN t
    have hcolu : Multiplicative.toAdd (F.FZ.φ e) =
        Multiplicative.toAdd (F.FZ.φ ⟨eElt z (fun s => bN s t),
          eElt_mem_of_forall_mem hzZ _⟩) := by
      rw [hφa, G24Vertex2.toAdd_phi_eElt F.FZ.φ z hzZ hφ]
    have heq : e = ⟨eElt z (fun s => bN s t), eElt_mem_of_forall_mem hzZ _⟩ :=
      hFZinj (Multiplicative.toAdd.injective hcolu)
    calc F.b * z t * F.b⁻¹ = (e : G) := (coe_conjE hZ2N bP zP).symm
      _ = eElt z (fun s => bN s t) := by rw [heq]
  have hkct : ∀ t, F.k * z t * F.k⁻¹ = z t := by
    intro t
    have h := F.cent_Z (z t) (hzZ t)
    calc F.k * z t * F.k⁻¹ = z t * F.k * F.k⁻¹ := by rw [h]
      _ = z t := by rw [mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨z, hzZ, hind, hact, hbct, hkct⟩

theorem G24Frame2.zBasis_spec [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {zb : Fin 4 → G} (hz : F.IsZBasis zb) :
    (∀ t, zb t ^ 2 = 1) ∧ (∀ t s, zb t * zb s = zb s * zb t) ∧
    (∀ t, ∀ x ∈ dsQ L2 L1 S, zb t * x = x * zb t) ∧ Function.Injective (eElt zb) ∧
    ∀ y ∈ centerOf (dsQ L2 L1 S), ∃ u, y = eElt zb u := by
  obtain ⟨hZ, hind, ha, hb, hk⟩ := hz
  have hspec := F.special_data hD
  obtain ⟨-, -, -, hcent, hexp, -, -, -⟩ := hspec
  have hsq : ∀ t, zb t ^ 2 = 1 := fun t => hexp (zb t) (hZ t)
  have hcomm : ∀ t s, zb t * zb s = zb s * zb t := fun t s =>
    hcent (zb t) (hZ t) (zb s) (hZ s).1
  have hcentral : ∀ t, ∀ x ∈ dsQ L2 L1 S, zb t * x = x * zb t := fun t x hx =>
    hcent (zb t) (hZ t) x hx
  have hinj : Function.Injective (eElt zb) :=
    eElt_injective ⟨fun t => (pow_two (zb t)).symm.trans (hsq t), hcomm, hind⟩
  refine ⟨hsq, hcomm, hcentral, hinj, ?_⟩
  intro y hy
  let F' : (Fin 4 → ZMod 2) → ↥(centerOf (dsQ L2 L1 S)) :=
    fun u => ⟨eElt zb u, eElt_mem_of_forall_mem hZ u⟩
  have hF'inj : Function.Injective F' := by
    intro u v h
    exact hinj (congrArg Subtype.val h)
  have hdom : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    norm_num
  have hcod : Nat.card ↥(centerOf (dsQ L2 L1 S)) = 16 := by
    rw [hD.card_center_right]; norm_num
  have hbij : Function.Bijective F' :=
    (Nat.bijective_iff_injective_and_card F').mpr
      ⟨hF'inj, by rw [hdom, hcod]⟩
  obtain ⟨u, hu⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨u, (congrArg Subtype.val hu).symm⟩

end CFSG.Quasithin.F112R.St84
