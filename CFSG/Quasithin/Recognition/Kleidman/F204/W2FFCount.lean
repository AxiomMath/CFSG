module

public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FF
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFFix
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFOrder

public section

namespace CFSG.Quasithin.Kleidman.F204

open Subgroup

theorem card_eq_relIndex_mul {G : Type*} [Group G] [Finite G] {V Z : Subgroup G} :
    Nat.card V = (V ⊓ Z).relIndex V * Nat.card (V ⊓ Z : Subgroup G) := by
  have h := Subgroup.relIndex_mul_card (H := V ⊓ Z) (K := V)
  rw [inf_eq_left.mpr inf_le_left] at h
  exact h.symm

theorem card_mul_le_card_of_inf_eq_bot {G : Type*} [Group G] [Finite G] {V C₁ C₂ : Subgroup G}
    (h1 : C₁ ≤ V) (h2 : C₂ ≤ V) (hinf : C₁ ⊓ C₂ = ⊥) :
    Nat.card C₁ * Nat.card C₂ ≤ Nat.card V := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : ↥C₁ × ↥C₂ => (⟨(p.1 : G) * p.2, mul_mem (h1 p.1.2) (h2 p.2.2)⟩ : ↥V)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' : (a : G) * b = a' * b' := congrArg Subtype.val h
  have e : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
    have ha : (a : G) = a' * b' * (b : G)⁻¹ := by
      rw [← h']
      group
    rw [ha]
    group
  have hx : (a' : G)⁻¹ * a ∈ C₁ ⊓ C₂ := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem a'.2) a.2, ?_⟩
    rw [e]
    exact mul_mem b'.2 (inv_mem b.2)
  rw [hinf, Subgroup.mem_bot] at hx
  have ha : (a : G) = a' := (inv_mul_eq_one.mp hx).symm
  have hb1 : (b' : G) * (b : G)⁻¹ = 1 := by
    rw [← e, hx]
  have hb : (b : G) = b' := (mul_inv_eq_one.mp hb1).symm
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

theorem card_inf_centralizer_conj {G : Type*} [Group G] [Finite G] {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (S : Subgroup G) :
    Nat.card ((V ⊓ Subgroup.centralizer (S : Set G) : Subgroup G)) =
      Nat.card ((V ⊓ Subgroup.centralizer
        ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) : Subgroup G)) := by
  have hV : ∀ v : G, v ∈ V → g * v * g⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hg v).mp hv
  have hV' : ∀ v : G, v ∈ V → g⁻¹ * v * g ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
  have fwd : ∀ v : G, v ∈ V ⊓ Subgroup.centralizer (S : Set G) →
      g * v * g⁻¹ ∈ V ⊓ Subgroup.centralizer
        ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro v hv
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨hV v hvV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hs' : s * v = v * s := Subgroup.mem_centralizer_iff.mp hvC s hs
    show g * s * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * s * g⁻¹)
    calc g * s * g⁻¹ * (g * v * g⁻¹) = g * (s * v) * g⁻¹ := by group
      _ = g * (v * s) * g⁻¹ := by rw [hs']
      _ = g * v * g⁻¹ * (g * s * g⁻¹) := by group
  have bwd : ∀ w : G, w ∈ V ⊓ Subgroup.centralizer
        ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) →
      g⁻¹ * w * g ∈ V ⊓ Subgroup.centralizer (S : Set G) := by
    intro w hw
    obtain ⟨hwV, hwC⟩ := Subgroup.mem_inf.mp hw
    refine Subgroup.mem_inf.mpr ⟨hV' w hwV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hmem : g * s * g⁻¹ ∈ ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.mem_map_of_mem _ hs
    have hw' : (g * s * g⁻¹) * w = w * (g * s * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hwC _ hmem
    show s * (g⁻¹ * w * g) = g⁻¹ * w * g * s
    calc s * (g⁻¹ * w * g) = g⁻¹ * ((g * s * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * s * g⁻¹)) * g := by rw [hw']
      _ = g⁻¹ * w * g * s := by group
  exact Nat.card_congr
    { toFun := fun v => ⟨g * (v : G) * g⁻¹, fwd _ v.2⟩
      invFun := fun w => ⟨g⁻¹ * (w : G) * g, bwd _ w.2⟩
      left_inv := fun v => Subtype.ext (by
        show g⁻¹ * (g * (v : G) * g⁻¹) * g = v
        group)
      right_inv := fun w => Subtype.ext (by
        show g * (g⁻¹ * (w : G) * g) * g⁻¹ = w
        group) }

theorem map_subtype_conj {G : Type*} [Group G] {L : Subgroup G} (A : Subgroup L) (g : L) :
    ((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G) =
      (A.map L.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_map_conj {L N : Type*} [Group L] [Group N] (φ : L →* N) (B : Subgroup L) (g : L) :
    (B.map (MulAut.conj g).toMonoidHom).map φ =
      (B.map φ).map (MulAut.conj (φ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

theorem exists_not_mem_normalizer_of_card_four (K : Subgroup (alternatingGroup (Fin 5)))
    (hK : Nat.card K = 4) :
    ∃ x : alternatingGroup (Fin 5), x ∉ Subgroup.normalizer (K : Set (alternatingGroup (Fin 5))) := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have htop : Subgroup.normalizer (K : Set (alternatingGroup (Fin 5))) = ⊤ :=
    eq_top_iff.mpr fun x _ => hcon x
  have hN : K.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases Subgroup.Normal.eq_bot_or_eq_top K with hb | ht
  · rw [hb, Subgroup.card_bot] at hK
    norm_num at hK
  · rw [ht, Subgroup.card_top, natCard_alt5] at hK
    norm_num at hK

theorem map_conj_ne {G : Type*} [Group G] (K : Subgroup G) (x : G)
    (hx : x ∉ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj x).toMonoidHom ≠ K := by
  intro h
  apply hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hm : x * y * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    rw [h] at hm
    exact hm
  · intro hy
    have hm : x * y * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom := by
      rw [h]
      exact hy
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hm
    have this : x * k * x⁻¹ = x * y * x⁻¹ := hkeq
    have hky : k = y := mul_left_cancel (mul_right_cancel this)
    rw [← hky]
    exact hk

theorem card_le_of_square_le {n c : ℕ} (hn : n = 4 * c) (hsq : c * c ≤ n) (hn16 : 16 ≤ n) :
    n = 16 ∧ c = 4 := by
  have hc4 : c ≤ 4 := by nlinarith
  omega

theorem fa5_ff_card {G : Type*} [Group G] [Finite G] {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (φ : L →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    (hCL : ∀ v ∈ V, (∀ l : L, v * (l : G) = (l : G) * v) → v = 1)
    {A : Subgroup L} (hA : IsPGroup 2 A)
    (hAnt : ∃ a ∈ A, ∃ v ∈ V, (a : G) * v ≠ v * (a : G))
    (hidx : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V
      ≤ Nat.card (A.map φ)) :
    Nat.card V = 16 ∧ Nat.card (A.map φ) = 4 ∧
      Nat.card ((V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G) : Subgroup G))
        = 4 ∧
      ∃ A₂ : Subgroup L, IsPGroup 2 A₂ ∧ Nat.card (A₂.map φ) = 4 ∧ A₂.map φ ≠ A.map φ ∧
        Nat.card ((V ⊓ Subgroup.centralizer ((A₂.map L.subtype : Subgroup G) : Set G) :
          Subgroup G)) = 4 ∧
        (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)) ⊓
          (V ⊓ Subgroup.centralizer ((A₂.map L.subtype : Subgroup G) : Set G)) = ⊥ := by
  obtain ⟨a, ha, v0, hv0, hne0⟩ := hAnt
  have hnc : ∃ l : L, ∃ v ∈ V, ¬ Commute (l : G) v := ⟨a, v0, hv0, hne0⟩
  have h16 : 16 ≤ Nat.card V := sixteen_le_card_V hV2 hLV φ hφ hker hnc
  have hK1 : Nat.card (A.map φ) = 4 :=
    card_image_eq_four hV2 hLV φ hφ hker hA ⟨a, ha, v0, hv0, hne0⟩ hidx
  have hr1 : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)).relIndex V = 4 :=
    relIndex_eq_four hV2 hLV φ hφ hker hA ⟨a, ha, v0, hv0, hne0⟩ hidx
  obtain ⟨x, hx⟩ := exists_not_mem_normalizer_of_card_four (A.map φ) hK1
  obtain ⟨g, hg⟩ := hφ x
  have hA₂ : IsPGroup 2 (A.map (MulAut.conj g).toMonoidHom) := hA.map _
  have hmapA₂ : (A.map (MulAut.conj g).toMonoidHom).map φ =
      (A.map φ).map (MulAut.conj x).toMonoidHom := by
    rw [map_map_conj, hg]
  have hinjx : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hK₂ : Nat.card ((A.map (MulAut.conj g).toMonoidHom).map φ) = 4 := by
    rw [hmapA₂, Subgroup.card_map_of_injective hinjx, hK1]
  have hne : (A.map (MulAut.conj g).toMonoidHom).map φ ≠ A.map φ := by
    rw [hmapA₂]
    exact map_conj_ne _ x hx
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := hLV g.2
  have hS : ((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G) =
      (A.map L.subtype).map (MulAut.conj (g : G)).toMonoidHom := map_subtype_conj A g
  have hcardC : Nat.card ((V ⊓ Subgroup.centralizer
      ((((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G)) : Set G) :
        Subgroup G)) =
      Nat.card ((V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G) :
        Subgroup G)) := by
    rw [hS]
    exact (card_inf_centralizer_conj hgN _).symm
  have e1 : Nat.card V = 4 * Nat.card ((V ⊓ Subgroup.centralizer
      ((A.map L.subtype : Subgroup G) : Set G) : Subgroup G)) := by
    rw [card_eq_relIndex_mul (V := V)
      (Z := Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)), hr1]
  have hinf : (V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G)) ⊓
      (V ⊓ Subgroup.centralizer
        ((((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G)) : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨hvV, hvC1⟩ := Subgroup.mem_inf.mp hv1
    obtain ⟨-, hvC2⟩ := Subgroup.mem_inf.mp hv2
    have k1 : ∀ a ∈ A, v * (a : G) = (a : G) * v := fun a ha' =>
      (Subgroup.mem_centralizer_iff.mp hvC1 (a : G)
        (Subgroup.mem_map.mpr ⟨a, ha', rfl⟩)).symm
    have k2 : ∀ a ∈ A.map (MulAut.conj g).toMonoidHom,
        v * (a : G) = (a : G) * v := fun a ha' =>
      (Subgroup.mem_centralizer_iff.mp hvC2 (a : G)
        (Subgroup.mem_map.mpr ⟨a, ha', rfl⟩)).symm
    exact Subgroup.mem_bot.mpr
      (klein_fixed_inf_eq_bot φ hker hCL hK1 hK₂ hne.symm v hvV k1 k2)
  have hprod := card_mul_le_card_of_inf_eq_bot
    (inf_le_left : V ⊓ Subgroup.centralizer ((A.map L.subtype : Subgroup G) : Set G) ≤ V)
    (inf_le_left : V ⊓ Subgroup.centralizer
      ((((A.map (MulAut.conj g).toMonoidHom).map L.subtype : Subgroup G)) : Set G) ≤ V) hinf
  rw [hcardC] at hprod
  have hn16 : Nat.card V = 16 ∧ Nat.card ((V ⊓ Subgroup.centralizer
      ((A.map L.subtype : Subgroup G) : Set G) : Subgroup G)) = 4 :=
    card_le_of_square_le e1 hprod h16
  refine ⟨hn16.1, hK1, hn16.2, A.map (MulAut.conj g).toMonoidHom, hA₂, hK₂, hne, ?_, hinf⟩
  rw [hcardC]
  exact hn16.2

end CFSG.Quasithin.Kleidman.F204

end
