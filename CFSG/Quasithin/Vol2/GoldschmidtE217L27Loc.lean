module

public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Aut
public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Tri
public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Fun

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 E217R3

namespace E217L27

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G} {x z : G}

theorem exists_bfun (h : Hyp2 H T M V) (hTmax : IsMaxSubgroupIn H T)
    (hlt : (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8)
    (d : DihedralPair H T V (V ⊓ pCoreOf 2 H) x z) {b : G} (hb : b ∈ V ⊓ pCoreOf 2 H)
    (hbZ : b ∉ dpZ V z) :
    ∃ (Γ : Type) (_ : Group Γ) (ρ : ↥H →* Γ) (f : ↥H → Γ),
      BFun ρ f (T.subgroupOf H) ⟨x, d.VH d.xV⟩ ⟨z, d.zH⟩ ∧ f 1 ≠ 1 := by
  obtain ⟨hTB, hZc⟩ := aut_facts h hTmax hlt d
  obtain ⟨h3, -, -⟩ := pair_counts h d
  have hz3 : z ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one z
  set Q := pCoreOf 2 H with hQ
  set Z := dpZ V z with hZ
  have hbH : b ∈ H := d.VH hb.1
  have hxH : x ∈ H := d.VH d.xV
  have hbP : b ∈ dpP H V (V ⊓ Q) z := Subgroup.mem_sup_left hb
  have hZc' : ∀ ζ ∈ Z.subgroupOf H, ∀ g : ↥H, g * ζ = ζ * g := fun ζ hζ g =>
    Subtype.ext (hZc ζ (Subgroup.mem_subgroupOf.1 hζ) g g.2)
  have hN : (Z.subgroupOf H).Normal :=
    ⟨fun n hn g => by
      have := hZc' n hn g
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
      exact hn⟩
  set ρ : ↥H →* ↥H ⧸ Z.subgroupOf H := QuotientGroup.mk' (Z.subgroupOf H) with hρ
  have hker : ∀ g : ↥H, ρ g = 1 ↔ (g : G) ∈ Z := fun g => by
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set bH : ↥H := ⟨b, hbH⟩ with hbHdef
  set xH : ↥H := ⟨x, hxH⟩ with hxHdef
  set zH : ↥H := ⟨z, d.zH⟩ with hzHdef
  have hb2 : b * b = 1 := by simpa [pow_two] using h.hyp.elem.2 b hb.1
  have hBsq : ∀ c : ↥H, (c : G) ∈ V ⊓ Q → c * c = 1 := fun c hc =>
    Subtype.ext (by simpa [pow_two] using h.hyp.elem.2 c hc.1)
  have hbb : bH * bH = 1 := Subtype.ext hb2
  have hconjB : ∀ t : ↥H, (t : G) ∈ T → ∀ c : ↥H, (c : G) ∈ V ⊓ Q →
      ρ t * ρ c * (ρ t)⁻¹ = ρ c := by
    intro t ht c hc
    have h1 : ρ (t * c * t⁻¹ * c⁻¹) = 1 := by
      refine (hker _).2 ?_
      simpa using hTB t ht c hc
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_one.1 h1
  have hβ : ∀ g : ↥H, (((g * bH * g⁻¹) * (xH * (g * bH * g⁻¹) * xH⁻¹) : ↥H) : G) ∈ V ⊓ Q := by
    intro g
    have hqQ : (g : G) * b * (g : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H g.2) b).mp
        hb.2
    have hqq : ((g : G) * b * (g : G)⁻¹) * ((g : G) * b * (g : G)⁻¹) = 1 := by
      calc ((g : G) * b * (g : G)⁻¹) * ((g : G) * b * (g : G)⁻¹) = g * (b * b) * (g : G)⁻¹ := by
            group
        _ = 1 := by rw [hb2]; group
    have hxq : x * ((g : G) * b * (g : G)⁻¹) * x⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hxH) _).mp
        hqQ
    have hqx : ((g : G) * b * (g : G)⁻¹) * x * ((g : G) * b * (g : G)⁻¹)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.hyp.normal_T (d.QT hqQ)) x).mp d.xV
    have hqi : ((g : G) * b * (g : G)⁻¹)⁻¹ = (g : G) * b * (g : G)⁻¹ :=
      inv_eq_of_mul_eq_one_right hqq
    refine ⟨?_, Q.mul_mem hqQ hxq⟩
    have e : ((g : G) * b * (g : G)⁻¹) * (x * ((g : G) * b * (g : G)⁻¹) * x⁻¹) =
        (((g : G) * b * (g : G)⁻¹) * x * ((g : G) * b * (g : G)⁻¹)⁻¹) * x⁻¹ := by
      rw [hqi]; group
    show ((g : G) * b * (g : G)⁻¹) * (x * ((g : G) * b * (g : G)⁻¹) * x⁻¹) ∈ V
    rw [e]
    exact V.mul_mem hqx (V.inv_mem d.xV)
  have hPmem : ∀ w : G, w ∈ dpP H V (V ⊓ Q) z → ((w : G) ∈ dpP H V (V ⊓ Q) z) := fun w hw => hw
  have hzP : z * b * z⁻¹ ∈ dpP H V (V ⊓ Q) z :=
    (Subgroup.mem_normalizer_iff.mp (d.IP d.zI) b).mp hbP
  have hzP' : z⁻¹ * b * z ∈ dpP H V (V ⊓ Q) z := by
    have := (Subgroup.mem_normalizer_iff.mp (d.IP ((dpI V z).inv_mem d.zI)) b).mp hbP
    simpa using this
  have hcommP : ∀ a w : ↥H, (a : G) ∈ dpP H V (V ⊓ Q) z → (w : G) ∈ dpP H V (V ⊓ Q) z →
      ρ a * ρ w = ρ w * ρ a := by
    intro a w ha hw
    have h1 : ρ (a * w * a⁻¹ * w⁻¹) = 1 := by
      refine (hker _).2 ?_
      exact d.comm_mem_Z ha hw
    simp only [map_mul, map_inv] at h1
    exact (commutatorElement_eq_one_iff_mul_comm (g₁ := ρ a) (g₂ := ρ w)).1
      (by rw [commutatorElement_def]; exact h1)
  refine ⟨↥H ⧸ Z.subgroupOf H, inferInstance, ρ, fun g => ρ (g * bH * g⁻¹),
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro g
    show ρ (g * bH * g⁻¹) * ρ (g * bH * g⁻¹) = 1
    rw [← map_mul]
    have : (g * bH * g⁻¹) * (g * bH * g⁻¹) = 1 := by
      calc (g * bH * g⁻¹) * (g * bH * g⁻¹) = g * (bH * bH) * g⁻¹ := by group
        _ = 1 := by rw [hbb]; group
    rw [this, map_one]
  ·
    intro g t ht
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have h1 := hconjB t htT bH ⟨hb.1, hb.2⟩
    show ρ (g * t * bH * (g * t)⁻¹) = ρ (g * bH * g⁻¹)
    have e : g * t * bH * (g * t)⁻¹ = g * (t * bH * t⁻¹) * g⁻¹ := by group
    rw [e]
    simp only [map_mul, map_inv] at h1 ⊢
    rw [h1]
  ·
    intro g₁ g₂
    show ρ (g₁ * g₂ * bH * (g₁ * g₂)⁻¹) = ρ g₁ * ρ (g₂ * bH * g₂⁻¹) * (ρ g₁)⁻¹
    simp only [map_mul, map_inv]
    group
  ·
    have e1 : ρ ((1 : ↥H) * bH * (1 : ↥H)⁻¹) = ρ bH := by simp
    have hb' : (bH : G) ∈ dpP H V (V ⊓ Q) z := hbP
    have hw1 : ((zH * bH * zH⁻¹ : ↥H) : G) ∈ dpP H V (V ⊓ Q) z := by
      simpa using hzP
    have hw2 : ((zH⁻¹ * bH * zH : ↥H) : G) ∈ dpP H V (V ⊓ Q) z := by
      simpa using hzP'
    have hprod : ρ (bH * (zH * bH * zH⁻¹) * (zH⁻¹ * bH * zH)) = 1 := by
      refine (hker _).2 ?_
      exact triple_rel d hz3 hb
    show Triple3 (ρ ((1 : ↥H) * bH * (1 : ↥H)⁻¹)) (ρ (zH * bH * zH⁻¹)) (ρ (zH⁻¹ * bH * zH⁻¹⁻¹))
    rw [e1, inv_inv]
    refine ⟨?_, hcommP _ _ hb' hw1, hcommP _ _ hb' hw2, hcommP _ _ hw1 hw2⟩
    simpa [map_mul] using hprod
  ·
    intro g t ht
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have hβg := hβ g
    show ρ (t * g * bH * (t * g)⁻¹) * ρ (t * xH * g * bH * (t * xH * g)⁻¹) =
      ρ (g * bH * g⁻¹) * ρ (xH * g * bH * (xH * g)⁻¹)
    have e1 : ρ (t * g * bH * (t * g)⁻¹) * ρ (t * xH * g * bH * (t * xH * g)⁻¹) =
        ρ t * (ρ (g * bH * g⁻¹) * ρ (xH * (g * bH * g⁻¹) * xH⁻¹)) * (ρ t)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    have e2 : ρ (g * bH * g⁻¹) * ρ (xH * g * bH * (xH * g)⁻¹) =
        ρ (g * bH * g⁻¹) * ρ (xH * (g * bH * g⁻¹) * xH⁻¹) := by
      simp only [map_mul, map_inv]
      group
    have h1 := hconjB t htT _ hβg
    simp only [map_mul, map_inv] at h1
    rw [e1, e2]
    simp only [map_mul, map_inv]
    simpa [mul_assoc] using h1
  ·
    intro g
    have hβg := hβ g
    show ρ (g * bH * g⁻¹) * ρ (xH * g * bH * (xH * g)⁻¹) *
      (ρ (g * bH * g⁻¹) * ρ (xH * g * bH * (xH * g)⁻¹)) = 1
    have e : ρ (g * bH * g⁻¹) * ρ (xH * g * bH * (xH * g)⁻¹) =
        ρ ((g * bH * g⁻¹) * (xH * (g * bH * g⁻¹) * xH⁻¹)) := by
      simp only [map_mul, map_inv]
      group
    rw [e, ← map_mul, hBsq _ hβg, map_one]
  ·
    intro h1
    have : ρ bH = 1 := by simpa using h1
    exact hbZ ((hker bH).1 this)

end E217L27

end CFSG.Quasithin
