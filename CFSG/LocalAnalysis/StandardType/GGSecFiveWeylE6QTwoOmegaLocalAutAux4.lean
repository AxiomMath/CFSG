module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux3

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

@[expose] public def NL (L Bs : Subgroup G) : Subgroup G := L ⊓ Subgroup.normalizer (Bs : Set G)

public theorem mem_NL {L Bs : Subgroup G} {g : G} :
    g ∈ NL L Bs ↔ g ∈ L ∧ g ∈ Subgroup.normalizer (Bs : Set G) :=
  Subgroup.mem_inf

public theorem NL_le_normalizer_inf (L Bs : Subgroup G) :
    NL L Bs ≤ Subgroup.normalizer ((Bs ⊓ L : Subgroup G) : Set G) := by
  intro g hg
  obtain ⟨hgL, hgN⟩ := mem_NL.mp hg
  rw [Subgroup.mem_normalizer_iff] at hgN ⊢
  intro x
  constructor
  · intro hx
    exact ⟨(hgN x).mp hx.1, L.mul_mem (L.mul_mem hgL hx.2) (L.inv_mem hgL)⟩
  · intro hx
    refine ⟨(hgN x).mpr hx.1, ?_⟩
    have hxl : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hxl]
    exact L.mul_mem (L.mul_mem (L.inv_mem hgL) hx.2) hgL

@[expose] public def conjBs (L Bs : Subgroup G) : ↥(NL L Bs) →* MulAut ↥Bs :=
  (Subgroup.normalizerMonoidHom (H := Bs)).comp (Subgroup.inclusion inf_le_right)

@[expose] public def conjE (L Bs : Subgroup G) : ↥(NL L Bs) →* MulAut ↥(Bs ⊓ L) :=
  (Subgroup.normalizerMonoidHom (H := Bs ⊓ L)).comp
    (Subgroup.inclusion (NL_le_normalizer_inf L Bs))

public theorem conjBs_coe (L Bs : Subgroup G) (l : ↥(NL L Bs)) (b : ↥Bs) :
    ((conjBs L Bs l) b : G) = (l : G) * (b : G) * (l : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe Bs _ b

public theorem conjE_coe (L Bs : Subgroup G) (l : ↥(NL L Bs)) (e : ↥(Bs ⊓ L)) :
    ((conjE L Bs l) e : G) = (l : G) * (e : G) * (l : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe (Bs ⊓ L) _ e

public theorem ggAutomizer_eq_range_conjBs (L Bs : Subgroup G) :
    ggAutomizer L Bs = (conjBs L Bs).range := by
  rw [ggAutomizer]
  have hset : ggInduced L Bs = Set.range (conjBs L Bs) := by
    ext φ
    constructor
    · rintro ⟨g, hgL, hgN, hφ⟩
      exact ⟨⟨g, mem_NL.mpr ⟨hgL, hgN⟩⟩, MulEquiv.ext fun b => Subtype.ext (by
        rw [conjBs_coe]; exact (hφ b).symm)⟩
    · rintro ⟨l, rfl⟩
      exact ⟨(l : G), (mem_NL.mp l.2).1, (mem_NL.mp l.2).2, fun b => conjBs_coe L Bs l b⟩
  rw [hset]
  exact le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx) Subgroup.subset_closure

public theorem bstar_eq_sup {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hxBs : x ∈ Bs) (hord : orderOf x = 3)
    (hExbot : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥) :
    Bs = (Bs ⊓ L) ⊔ Subgroup.zpowers x := by
  have hcompl : Subgroup.IsComplement' (EB Bs L) ((Subgroup.zpowers x).subgroupOf Bs) :=
    bstar_isComplement hBs hcard hcardE hxBs hord hExbot
  have htop : EB Bs L ⊔ (Subgroup.zpowers x).subgroupOf Bs = ⊤ :=
    Subgroup.IsComplement'.sup_eq_top hcompl
  have hmap := congrArg (Subgroup.map (Subgroup.subtype Bs)) htop
  have hbot : (⊤ : Subgroup ↥Bs).map (Subgroup.subtype Bs) = Bs := by
    rw [← Subgroup.subgroupOf_self Bs, Subgroup.map_subgroupOf_eq_of_le (le_refl Bs)]
  have hEB : EB Bs L = (Bs ⊓ L).subgroupOf Bs := rfl
  have hEB' : (Subgroup.zpowers x).subgroupOf Bs
      = ((Subgroup.zpowers x).subgroupOf Bs) := rfl
  rw [hEB, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hxBs), hbot] at hmap
  exact hmap.symm

public theorem conj_eq_self_of_sup {Bs E Z : Subgroup G} {g : G} (hsup : Bs = E ⊔ Z)
    (hE : ∀ e ∈ E, g * e * g⁻¹ = e) (hZ : ∀ z ∈ Z, g * z * g⁻¹ = z) :
    ∀ b ∈ Bs, g * b * g⁻¹ = b := by
  intro b hb
  rw [hsup, Subgroup.sup_eq_closure] at hb
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact hE x hx
      · exact hZ x hx
  | one => simp
  | mul x y _ _ ihx ihy =>
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = x * y := by rw [ihx, ihy]
  | inv x _ ihx =>
      calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [ihx]

public theorem ker_conjE_eq_ker_conjBs {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hxBs : x ∈ Bs) (hord : orderOf x = 3)
    (hExbot : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    (conjE L Bs).ker = (conjBs L Bs).ker := by
  have hsup : Bs = (Bs ⊓ L) ⊔ Subgroup.zpowers x :=
    bstar_eq_sup hBs hcard hcardE hxBs hord hExbot
  ext l
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  ·
    intro h
    have hE : ∀ e ∈ Bs ⊓ L, (l : G) * e * (l : G)⁻¹ = e := by
      intro e he
      have h1 := congrArg (fun z : ↥(Bs ⊓ L) => (z : G)) (DFunLike.congr_fun h ⟨e, he⟩)
      rw [conjE_coe] at h1
      simpa using h1
    have hx' : (l : G) * x * (l : G)⁻¹ = x := by
      have h0 : (l : G) * x = x * (l : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2.1)
      rw [h0]
      group
    have hZ : ∀ z ∈ Subgroup.zpowers x, (l : G) * z * (l : G)⁻¹ = z := by
      intro z hz
      have hx'' : (l : G) * x = x * (l : G) := by
        calc (l : G) * x = (l * x * (l : G)⁻¹) * (l : G) := by group
          _ = x * (l : G) := by rw [hx']
      have hxcent : x ∈ Subgroup.centralizer ({(l : G)} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hx''.symm
      have h1 : z ∈ Subgroup.centralizer ({(l : G)} : Set G) :=
        (Subgroup.zpowers_le (H := Subgroup.centralizer ({(l : G)} : Set G))).mpr hxcent hz
      have h2 : (l : G) * z = z * (l : G) :=
        (Subgroup.mem_centralizer_singleton_iff.mp h1).symm
      rw [h2]
      group
    have hall := conj_eq_self_of_sup hsup hE hZ
    exact MulEquiv.ext fun b => Subtype.ext (hall b b.2)
  ·
    intro h
    have hE : ∀ e ∈ Bs ⊓ L, (l : G) * e * (l : G)⁻¹ = e := by
      intro e he
      have h1 := congrArg (fun z : ↥Bs => (z : G))
        (DFunLike.congr_fun h ⟨e, he.1⟩)
      rw [conjBs_coe] at h1
      simpa using h1
    exact MulEquiv.ext fun e => Subtype.ext (hE e e.2)

public theorem card_ggAutomizer_eq_card_range_conjE {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hxBs : x ∈ Bs) (hord : orderOf x = 3)
    (hExbot : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    Nat.card (ggAutomizer L Bs) = Nat.card ↥(conjE L Bs).range := by
  have hker := ker_conjE_eq_ker_conjBs hBs hcard hcardE hxBs hord hExbot hLx
  have h1 := Subgroup.card_ker_mul_card_range (conjBs L Bs)
  have h2 := Subgroup.card_ker_mul_card_range (conjE L Bs)
  have hpos : 0 < Nat.card ↥(conjBs L Bs).ker := Nat.card_pos
  have heq : Nat.card ↥(conjBs L Bs).ker * Nat.card ↥(conjBs L Bs).range
      = Nat.card ↥(conjBs L Bs).ker * Nat.card ↥(conjE L Bs).range := by
    rw [h1, ← hker, h2]
  rw [ggAutomizer_eq_range_conjBs L Bs]
  exact Nat.eq_of_mul_eq_mul_left hpos heq

@[expose] public def qE (Bs L : Subgroup G) (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    ↥(Bs ⊓ L) →* ↥(Ebar Bs L θ) :=
  MonoidHom.codRestrict ((qMap (K := K) θ).comp (Subgroup.inclusion inf_le_right)) _
    fun e => Subgroup.mem_map_of_mem (qMap (K := K) θ) (mem_EL.mpr (Subgroup.mem_inf.mp e.2))

public theorem qE_apply (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (e : ↥(Bs ⊓ L)) :
    ((qE Bs L θ e : ↥(Ebar Bs L θ)) : OrthRest.RPlus K 4) = qMap (K := K) θ ⟨(e : G), e.2.2⟩ :=
  rfl

public theorem qE_injective (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hEbot : (Bs ⊓ L) ⊓ (Subgroup.center L).map L.subtype = ⊥) :
    Function.Injective (qE Bs L θ) := by
  intro a b hab
  have hab' : qMap (K := K) θ ⟨(a : G), a.2.2⟩ = qMap (K := K) θ ⟨(b : G), b.2.2⟩ :=
    congrArg Subtype.val hab
  apply Subtype.ext
  have h2 : (⟨(a : G), a.2.2⟩ : ↥L) * (⟨(b : G), b.2.2⟩ : ↥L)⁻¹ ∈ Subgroup.center ↥L := by
    rw [← qMap_ker (K := K) θ, MonoidHom.mem_ker, map_mul, map_inv, hab', mul_inv_cancel]
  have hbot : (a : G) * (b : G)⁻¹ ∈ (Bs ⊓ L) ⊓ (Subgroup.center L).map L.subtype := by
    refine ⟨⟨?_, ?_⟩, Subgroup.mem_map.mpr ⟨_, h2, rfl⟩⟩
    · exact Bs.mul_mem a.2.1 (Bs.inv_mem b.2.1)
    · exact L.mul_mem a.2.2 (L.inv_mem b.2.2)
  rw [hEbot] at hbot
  exact eq_of_mul_inv_eq_one (Subgroup.mem_bot.mp hbot)

public theorem qE_surjective (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    Function.Surjective (qE Bs L θ) := by
  intro y
  obtain ⟨e, he, hq⟩ := (mem_Ebar θ).mp y.2
  exact ⟨⟨(e : G), mem_EL.mp he⟩, Subtype.ext (by
    rw [qE_apply]
    show qMap (K := K) θ ⟨(e : G), (e : ↥L).2⟩ = (y : OrthRest.RPlus K 4)
    rw [hq])⟩

public noncomputable def ΘE (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥(Ebar Bs L θ))
    (hEbot : (Bs ⊓ L) ⊓ (Subgroup.center L).map L.subtype = ⊥) :
    ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3)) :=
  (MulEquiv.ofBijective (qE Bs L θ) ⟨qE_injective Bs L θ hEbot, qE_surjective Bs L θ⟩).trans
    Θ.symm

public theorem ΘE_apply (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥(Ebar Bs L θ))
    (hEbot : (Bs ⊓ L) ⊓ (Subgroup.center L).map L.subtype = ⊥) (e : ↥(Bs ⊓ L)) :
    Θ (ΘE Bs L θ Θ hEbot e) = qE Bs L θ e := by
  show Θ (Θ.symm (qE Bs L θ e)) = qE Bs L θ e
  rw [MulEquiv.apply_symm_apply]

end CFSG.StandardType.E6QTwo

end
