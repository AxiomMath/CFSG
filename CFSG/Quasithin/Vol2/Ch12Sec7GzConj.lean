module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzCount
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open

variable {G : Type*} [Group G]

abbrev cjS (x : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj x).toMonoidHom

theorem mem_cjS_iff {x : G} {K : Subgroup G} {y : G} : y ∈ cjS x K ↔ x⁻¹ * y * x ∈ K := by
  constructor
  · intro h
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp h
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hky
    have e : x⁻¹ * y * x = k := by rw [← hky]; group
    rw [e]
    exact hk
  · intro h
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * y * x, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem cjS_eq_of_mem_normalizer {x : G} {K : Subgroup G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) : cjS x K = K := by
  ext y
  rw [mem_cjS_iff]
  have hx' : x⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hx
  have h := Subgroup.mem_normalizer_iff.mp hx' y
  rw [inv_inv] at h
  exact h.symm

theorem mem_normalizer_of_cjS_eq {x : G} {K : Subgroup G} (h : cjS x K = K) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  have key : ∀ w : G, w ∈ K ↔ x⁻¹ * w * x ∈ K := fun w => by
    rw [← mem_cjS_iff, h]
  refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  constructor
  · intro hy
    apply (key (x * y * x⁻¹)).mpr
    rw [e]
    exact hy
  · intro hy
    have h2 := (key (x * y * x⁻¹)).mp hy
    rw [e] at h2
    exact h2

theorem cjS_one (K : Subgroup G) : cjS 1 K = K :=
  cjS_eq_of_mem_normalizer (Subgroup.one_mem _)

theorem cjS_mul (x y : G) (K : Subgroup G) : cjS (x * y) K = cjS x (cjS y K) := by
  ext w
  simp only [mem_cjS_iff]
  rw [show (x * y)⁻¹ * w * (x * y) = y⁻¹ * (x⁻¹ * w * x) * y by group]

theorem cjS_inf (x : G) (A B : Subgroup G) : cjS x (A ⊓ B) = cjS x A ⊓ cjS x B :=
  Subgroup.map_inf_eq A B _ (MulAut.conj x).injective

theorem card_cjS (x : G) (K : Subgroup G) : Nat.card (cjS x K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj x).injective

theorem cjS_injective (x : G) {A B : Subgroup G} (h : cjS x A = cjS x B) : A = B :=
  Subgroup.map_injective (MulAut.conj x).injective h

theorem isElemAbelian_cjS {p : ℕ} {x : G} {K : Subgroup G} (hK : IsElemAbelian p K) :
    IsElemAbelian p (cjS x K) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · show (a : G) * (b : G) = (b : G) * (a : G)
    have ha := mem_cjS_iff.mp a.2
    have hb := mem_cjS_iff.mp b.2
    have h : (x⁻¹ * (a : G) * x) * (x⁻¹ * (b : G) * x) =
        (x⁻¹ * (b : G) * x) * (x⁻¹ * (a : G) * x) :=
      congrArg Subtype.val (hK.1.is_comm.comm ⟨x⁻¹ * (a : G) * x, ha⟩ ⟨x⁻¹ * (b : G) * x, hb⟩)
    calc (a : G) * (b : G)
        = x * ((x⁻¹ * (a : G) * x) * (x⁻¹ * (b : G) * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * (b : G) * x) * (x⁻¹ * (a : G) * x)) * x⁻¹ := by rw [h]
      _ = (b : G) * (a : G) := by group
  · have hy' := mem_cjS_iff.mp hy
    have hp := hK.2 _ hy'
    calc y ^ p = (x * (x⁻¹ * y * x) * x⁻¹) ^ p := by
          rw [show x * (x⁻¹ * y * x) * x⁻¹ = y by group]
      _ = x * (x⁻¹ * y * x) ^ p * x⁻¹ := conj_pow
      _ = 1 := by rw [hp]; group

theorem le_relIndex_of_cjS [Finite G] {H V : Subgroup G} {ι : Type*} [Finite ι] (f : ι → G)
    (hfH : ∀ i, f i ∈ H) (hinj : Function.Injective fun i => cjS (f i) V) :
    Nat.card ι ≤ (H ⊓ Subgroup.normalizer (V : Set G)).relIndex H := by
  refine le_relIndex_of_fiber (fun i => (⟨f i, hfH i⟩ : H)) fun i j hij => ?_
  apply hinj
  have hN : (f i)⁻¹ * (f j) ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.mem_inf.mp hij).2
  show cjS (f i) V = cjS (f j) V
  have e : cjS (f j) V = cjS (f i) V := by
    rw [show f j = f i * ((f i)⁻¹ * f j) by group, cjS_mul, cjS_eq_of_mem_normalizer hN]
  exact e.symm

theorem relIndex_centralizer_conj {L : Subgroup G} {l x : G} (hl : l ∈ L) :
    (Subgroup.centralizer ({l * x * l⁻¹} : Set G)).relIndex L =
      (Subgroup.centralizer ({x} : Set G)).relIndex L := by
  have hmapL : cjS l L = L := cjS_eq_of_mem_normalizer (Subgroup.le_normalizer hl)
  have hmapC : cjS l (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({l * x * l⁻¹} : Set G) := by
    ext y
    rw [mem_cjS_iff, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc y * (l * x * l⁻¹) = l * ((l⁻¹ * y * l) * x) * l⁻¹ := by group
        _ = l * (x * (l⁻¹ * y * l)) * l⁻¹ := by rw [h]
        _ = (l * x * l⁻¹) * y := by group
    · intro h
      calc (l⁻¹ * y * l) * x = l⁻¹ * (y * (l * x * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * x * l⁻¹) * y) * l := by rw [h]
        _ = x * (l⁻¹ * y * l) := by group
  calc (Subgroup.centralizer ({l * x * l⁻¹} : Set G)).relIndex L
      = (cjS l (Subgroup.centralizer ({x} : Set G))).relIndex (cjS l L) := by
        rw [hmapC, hmapL]
    _ = (Subgroup.centralizer ({x} : Set G)).relIndex L :=
      Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj l).toMonoidHom) _ _
        (MulAut.conj l).injective

end CFSG.Quasithin.H13.I1277
