module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLieCoords
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K6c K7 LieFam811 IsLie811 IsSignedCoords qPlusPi)

variable {G : Type} [Group G] [Finite G] {D : Data G}

@[expose] def planeE : Subgroup (Multiplicative (Fin 3 → ZMod 3)) where
  carrier := {v | Multiplicative.toAdd v 2 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, toAdd_mul, Pi.add_apply] at *
    rw [ha, hb]
    simp
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, toAdd_inv, Pi.neg_apply] at *
    rw [ha]
    decide

instance : DecidablePred (· ∈ planeE) := fun v =>
  inferInstanceAs (Decidable (Multiplicative.toAdd v 2 = 0))

theorem card_planeE : Nat.card planeE = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem planeE_le_closure : planeE ≤ Subgroup.closure
    {Multiplicative.ofAdd ![1, 0, 0], Multiplicative.ofAdd ![0, 1, 0]} := by
  intro v hv
  have hv' : Multiplicative.toAdd v 2 = 0 := hv
  have h : v = Multiplicative.ofAdd ![1, 0, 0] ^ (Multiplicative.toAdd v 0).val *
      Multiplicative.ofAdd ![0, 1, 0] ^ (Multiplicative.toAdd v 1).val := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · simp
    · simp
    · simpa using hv'
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

@[expose] def GoodPoint (M : Subgroup G) (x : G) : Prop :=
  Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ M

omit [Finite G] in
theorem GoodPoint.conj {M : Subgroup G} {x g : G} (hg : g ∈ M) (hx : GoodPoint M x) :
    GoodPoint M (g * x * g⁻¹) := by
  intro y hy
  set f : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hmap : (Subgroup.zpowers (g * x * g⁻¹)).map f = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    congr 1
    simp [f, mul_assoc]
  have h1 : f y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    have := Subgroup.le_normalizer_map (H := Subgroup.zpowers (g * x * g⁻¹)) f
      (Subgroup.mem_map_of_mem f hy)
    rwa [hmap] at this
  have h2 : f y ∈ M := hx h1
  have : y = g * f y * g⁻¹ := by simp [f, mul_assoc]
  rw [this]
  exact M.mul_mem (M.mul_mem hg h2) (M.inv_mem hg)

theorem exists_perm_signs (v : Fin 3 → ZMod 3) (hv : v ≠ 0) (hz : ∃ i, v i = 0) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ((v = fun i => ε i * (![1, 0, 0] : Fin 3 → ZMod 3) (σ i)) ∨
        (v = fun i => ε i * (![1, 1, 0] : Fin 3 → ZMod 3) (σ i))) := by
  revert v
  decide +kernel

namespace Case811Sylow

variable {c : Ctx82E3 D}

structure SignedLift (h : Case811Sylow c) where
  c₀ : Multiplicative (Fin 3 → ZMod 3) →* c.Lbar
  a : Multiplicative (Fin 3 → ZMod 3) →* ↥c.L
  signed : IsSignedCoords h.Abar c₀
  range : a.range = h.A.subgroupOf c.L
  apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v
  inj_mk : Function.Injective
    ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp (h.A.subgroupOf c.L).subtype)
  inj : Function.Injective a
  mem : ∀ v, (a v : G) ∈ h.A
  order : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → orderOf ((a (Multiplicative.ofAdd v) : ↥c.L) : G) = 3

theorem SignedLift.nonempty (h : Case811Sylow c) (hK6c : K6c) {fam : LieFam811} {r f : ℕ}
    (hlie : IsLie811 c.Lbar fam r f) (hfam : fam ≠ .l4) : Nonempty (SignedLift h) := by
  obtain ⟨c₀, a, hs, hr, ha, hi, hinj, hm, ho⟩ := h.signed_coords_setup hK6c hlie hfam
  exact ⟨⟨c₀, a, hs, hr, ha, hi, hinj, hm, ho⟩⟩

namespace SignedLift

variable {h : Case811Sylow c} (s : SignedLift h)

@[expose] def pt (v : Fin 3 → ZMod 3) : G := ((s.a (Multiplicative.ofAdd v) : ↥c.L) : G)

theorem pt_mem_A (v : Fin 3 → ZMod 3) : s.pt v ∈ h.A := s.mem _

theorem pt_mem_L (v : Fin 3 → ZMod 3) : s.pt v ∈ c.L := (s.a _).2

theorem pt_zero : s.pt 0 = 1 := by simp [pt]

theorem pt_add (v w : Fin 3 → ZMod 3) : s.pt (v + w) = s.pt v * s.pt w := by
  simp [pt, ofAdd_add]

theorem pt_ne_one {v : Fin 3 → ZMod 3} (hv : v ≠ 0) : s.pt v ≠ 1 := by
  intro h1
  have := s.order v hv
  change orderOf (s.pt v) = 3 at this
  rw [h1, orderOf_one] at this
  omega

theorem pt_pow_three (v : Fin 3 → ZMod 3) : s.pt v ^ 3 = 1 := by
  by_cases hv : v = 0
  · subst hv
    simp [pt]
  · have h3 := s.order v hv
    change orderOf (s.pt v) = 3 at h3
    rw [← h3]
    exact pow_orderOf_eq_one _

theorem exists_pt_of_mem {x : G} (hx : x ∈ h.A) : ∃ v : Fin 3 → ZMod 3, s.pt v = x := by
  have hxL : (⟨x, h.A_le_L hx⟩ : ↥c.L) ∈ h.A.subgroupOf c.L := hx
  rw [← s.range] at hxL
  obtain ⟨w, hw⟩ := hxL
  exact ⟨Multiplicative.toAdd w, by simpa [pt] using congrArg Subtype.val hw⟩

theorem exists_conj (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) (hε : ∀ i, ε i ≠ 0) :
    ∃ g : ↥c.L, (g : G) ∈ Subgroup.normalizer (h.A : Set G) ∧ ∀ u : Fin 3 → ZMod 3,
      (g : G) * s.pt u * (g : G)⁻¹ = s.pt (fun i => ε i * u (σ i)) := by
  obtain ⟨n, hn⟩ := s.signed.2.2.2 σ ε hε
  have hnorm := h.mem_normalizer_of_coords (c₀ := s.c₀) s.signed.2.1
    (φ := fun v => Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) hn
  obtain ⟨g, hgN, -, hg⟩ := h.exists_conj_of_coords (c₀ := s.c₀) s.a s.range s.apply s.inj_mk
    (fun v => Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i))
    (n := n) (by simpa using hnorm) hn
  refine ⟨g, hgN, fun u => ?_⟩
  simpa [pt] using hg (Multiplicative.ofAdd u)

theorem orderOf_pt {v : Fin 3 → ZMod 3} (hv : v ≠ 0) : orderOf (s.pt v) = 3 := s.order v hv

theorem exists_pt_of_card_three {X : Subgroup G} (hXA : X ≤ h.A) (hX : Nat.card X = 3) :
    ∃ v : Fin 3 → ZMod 3, v ≠ 0 ∧ X = Subgroup.zpowers (s.pt v) := by
  have hnt : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx1⟩ := exists_ne (1 : X)
  obtain ⟨v, hv⟩ := s.exists_pt_of_mem (hXA x.2)
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    rw [← hv]
    simp [pt]
  refine ⟨v, hv0, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le, hv]
    exact x.2
  · rw [Nat.card_zpowers, s.orderOf_pt hv0, hX]

@[expose] def ptHom : Multiplicative (Fin 3 → ZMod 3) →* G := c.L.subtype.comp s.a

theorem ptHom_apply (v : Multiplicative (Fin 3 → ZMod 3)) :
    s.ptHom v = s.pt (Multiplicative.toAdd v) := rfl

theorem ptHom_injective : Function.Injective s.ptHom :=
  fun _ _ hxy => s.inj (Subtype.ext hxy)

theorem map_ptHom_le_A (S : Subgroup (Multiplicative (Fin 3 → ZMod 3))) :
    S.map s.ptHom ≤ h.A := by
  rintro _ ⟨v, -, rfl⟩
  exact s.mem v

theorem card_map_ptHom (S : Subgroup (Multiplicative (Fin 3 → ZMod 3))) :
    Nat.card (S.map s.ptHom) = Nat.card S :=
  Subgroup.card_map_of_injective s.ptHom_injective

theorem lbar_image_map_ptHom (S : Subgroup (Multiplicative (Fin 3 → ZMod 3))) :
    ((S.map s.ptHom).subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) =
      S.map s.c₀ := by
  have h1 : (S.map s.ptHom).subgroupOf c.L = S.map s.a := by
    have : S.map s.ptHom = (S.map s.a).map c.L.subtype := by
      rw [Subgroup.map_map]
      rfl
    rw [this]
    exact Subgroup.comap_map_eq_self_of_injective c.L.subtype_injective _
  rw [h1, Subgroup.map_map]
  congr 1
  ext v
  exact s.apply v

theorem zpowers_pt (v : Fin 3 → ZMod 3) :
    Subgroup.zpowers (s.pt v) = (Subgroup.zpowers (Multiplicative.ofAdd v)).map s.ptHom := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem lbar_image_zpowers_pt (v : Fin 3 → ZMod 3) :
    ((Subgroup.zpowers (s.pt v)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) =
      Subgroup.zpowers (s.c₀ (Multiplicative.ofAdd v)) := by
  rw [s.zpowers_pt, lbar_image_map_ptHom, MonoidHom.map_zpowers]

@[expose] def planeG : Subgroup G := planeE.map s.ptHom

theorem planeG_le_A : s.planeG ≤ h.A := s.map_ptHom_le_A _

theorem planeG_le_L : s.planeG ≤ c.L := s.planeG_le_A.trans h.A_le_L

theorem card_planeG : Nat.card s.planeG = 9 := by
  rw [planeG, card_map_ptHom, card_planeE]

theorem elemAbelian_planeG : CFSG.Open.IsElemAbelian 3 s.planeG :=
  h.elemAbelian.mono s.planeG_le_A

theorem lbar_image_planeG :
    (s.planeG.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) =
      Subgroup.closure {s.c₀ (Multiplicative.ofAdd ![1, 0, 0]),
        s.c₀ (Multiplicative.ofAdd ![0, 1, 0])} := by
  rw [planeG, lbar_image_map_ptHom]
  apply le_antisymm
  · calc planeE.map s.c₀
        ≤ (Subgroup.closure {Multiplicative.ofAdd ![1, 0, 0],
            Multiplicative.ofAdd ![0, 1, 0]}).map s.c₀ := Subgroup.map_mono planeE_le_closure
      _ = Subgroup.closure (s.c₀ '' {Multiplicative.ofAdd ![1, 0, 0],
            Multiplicative.ofAdd ![0, 1, 0]}) := MonoidHom.map_closure _ _
      _ = Subgroup.closure {s.c₀ (Multiplicative.ofAdd ![1, 0, 0]),
            s.c₀ (Multiplicative.ofAdd ![0, 1, 0])} := by rw [Set.image_pair]
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_map_of_mem _ (show Multiplicative.toAdd
        (Multiplicative.ofAdd (![1, 0, 0] : Fin 3 → ZMod 3)) 2 = 0 from rfl)
    · exact Subgroup.mem_map_of_mem _ (show Multiplicative.toAdd
        (Multiplicative.ofAdd (![0, 1, 0] : Fin 3 → ZMod 3)) 2 = 0 from rfl)

theorem n7_data (hN7 : K7Sp6Planes) {f p : ℕ} (hlie : IsLie811 c.Lbar .psp6 2 f)
    (hp : p ∈ D.sig) (hpq : p ∣ qPlusPi 2 f) :
    1 ≤ CFSG.Open.pRank p (Subgroup.centralizer
        ({s.c₀ (Multiplicative.ofAdd ![1, 0, 0]), s.c₀ (Multiplicative.ofAdd ![0, 1, 0])} :
          Set c.Lbar)) ∧
      ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) →
        2 ≤ CFSG.Open.pRank p (Subgroup.centralizer
          ({s.c₀ (Multiplicative.ofAdd v)} : Set c.Lbar)) :=
  by
  obtain ⟨h1, h2⟩ := hN7 c.Lbar f hlie p (D.sig_prime p hp).1 (c.five_le_of_mem_sigma hp) hpq
    h.Abar h.isElemAbelian_Abar h.card_Abar s.c₀ s.signed
  refine ⟨?_, fun v hv hz => ?_⟩
  · simpa only [CFSG.SectionRank.pRank_coe_eq_openPRank] using h1
  · simpa only [CFSG.SectionRank.pRank_coe_eq_openPRank] using h2 v hv hz

theorem pRank_inf_centralizer_planeG {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (s.planeG : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer
        ({s.c₀ (Multiplicative.ofAdd ![1, 0, 0]), s.c₀ (Multiplicative.ofAdd ![0, 1, 0])} :
          Set c.Lbar)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h1 := Ctx82E3.pRank_centralizer_lbar c (q := 3) (by norm_num) (p := p) hp2
    s.planeG_le_L (h.elemAbelian.isPGroup.to_le s.planeG_le_A)
  rw [h1, s.lbar_image_planeG, Subgroup.centralizer_closure]

theorem pRank_inf_centralizer_zpowers_pt {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (v : Fin 3 → ZMod 3) :
    CFSG.Open.pRank p (c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (s.pt v) : Set G)) =
      CFSG.Open.pRank p (Subgroup.centralizer
        ({s.c₀ (Multiplicative.ofAdd v)} : Set c.Lbar)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hX : Subgroup.zpowers (s.pt v) ≤ h.A := by
    rw [Subgroup.zpowers_le]
    exact s.pt_mem_A v
  have h1 := Ctx82E3.pRank_centralizer_lbar c (q := 3) (by norm_num) (p := p) hp2
    (hX.trans h.A_le_L) (h.elemAbelian.isPGroup.to_le hX)
  rw [h1, s.lbar_image_zpowers_pt, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem pt_mem_planeG_iff (w : Fin 3 → ZMod 3) : s.pt w ∈ s.planeG ↔ w 2 = 0 := by
  constructor
  · intro hw
    obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.mp hw
    have : u = Multiplicative.ofAdd w := s.ptHom_injective hu'
    subst this
    exact hu
  · intro hw
    exact Subgroup.mem_map.mpr ⟨Multiplicative.ofAdd w, hw, rfl⟩

theorem two_le_pRank_inf_normalizer_pt (hN7 : K7Sp6Planes) {f p : ℕ}
    (hlie : IsLie811 c.Lbar .psp6 2 f) (hp : p ∈ D.sig) (hpq : p ∣ qPlusPi 2 f)
    {v : Fin 3 → ZMod 3} (hv : v ≠ 0) (hz : ∃ i, v i = 0) :
    2 ≤ CFSG.Open.pRank p
      (D.M ⊓ Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G)) := by
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp2 : p ≠ 2 := by
    have := c.five_le_of_mem_sigma hp
    omega
  have h2 := (s.n7_data hN7 hlie hp hpq).2 v hv hz
  rw [← s.pRank_inf_centralizer_zpowers_pt hp2 v] at h2
  have hle : c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (s.pt v) : Set G) ≤
      D.M ⊓ Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G) :=
    inf_le_inf c.hyp81.1 (Subgroup.centralizer_le_normalizer _)
  exact h2.trans (CFSG.SectionRank.pRank_mono hp_prime.one_lt hle)

theorem good_of_mem_plane (hN7 : K7Sp6Planes) {f p : ℕ}
    (hlie : IsLie811 c.Lbar .psp6 2 f) (hp : p ∈ D.sig) (hpq : p ∣ qPlusPi 2 f)
    {v : Fin 3 → ZMod 3} (hv0 : v ≠ 0) (hv2 : v 2 = 0) : GoodPoint D.M (s.pt v) := by
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp2 : p ≠ 2 := by
    have := c.five_le_of_mem_sigma hp
    omega
  have h76 := c.conclusion76 hp
  have hEM : s.planeG ≤ D.M := s.planeG_le_L.trans c.hyp81.1
  have hcent : 0 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (s.planeG : Set G)) := by
    have h1 := (s.n7_data hN7 hlie hp hpq).1
    rw [← s.pRank_inf_centralizer_planeG hp2] at h1
    have hle : c.L ⊓ Subgroup.centralizer (s.planeG : Set G) ≤
        D.M ⊓ Subgroup.centralizer (s.planeG : Set G) := inf_le_inf c.hyp81.1 le_rfl
    have := h1.trans (CFSG.SectionRank.pRank_mono hp_prime.one_lt hle)
    omega
  have hN : ∀ X : Subgroup G, X ≤ s.planeG → Nat.card X = 3 →
      1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) := by
    intro X hXE hX3
    obtain ⟨w, hw0, rfl⟩ := s.exists_pt_of_card_three (hXE.trans s.planeG_le_A) hX3
    have hw2 : w 2 = 0 := (s.pt_mem_planeG_iff w).mp (hXE (Subgroup.mem_zpowers _))
    have := s.two_le_pRank_inf_normalizer_pt hN7 hlie hp hpq hw0 ⟨2, hw2⟩
    omega
  have hΓ := h76 3 Nat.prime_three s.planeG hEM s.elemAbelian_planeG
    (by rw [s.card_planeG]; norm_num) hcent hN
  have hXA : Subgroup.zpowers (s.pt v) ≤ h.A := by
    rw [Subgroup.zpowers_le]
    exact s.pt_mem_A v
  have hXE : Subgroup.zpowers (s.pt v) ≤ s.planeG := by
    rw [Subgroup.zpowers_le]
    exact (s.pt_mem_planeG_iff v).mpr hv2
  have hXab : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (s.pt v)) :=
    h.elemAbelian.mono hXA
  have h1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers (s.pt v)) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl _) hXab
      (by rw [Nat.card_zpowers, s.orderOf_pt hv0]; norm_num)
  have hcore := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
    (p := 3) (k := 1) (P := s.planeG) (Q := Subgroup.zpowers (s.pt v)) hXE h1
  have hle : Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G) ≤
      CFSG.Open.rankThreeGamma 1 3 s.planeG := by
    simpa [CFSG.Open.rankThreeGamma] using hcore
  exact hle.trans hΓ

theorem good_of_weight_le_two (hN7 : K7Sp6Planes) {f p : ℕ}
    (hlie : IsLie811 c.Lbar .psp6 2 f) (hp : p ∈ D.sig) (hpq : p ∣ qPlusPi 2 f)
    {v : Fin 3 → ZMod 3} (hv : v ≠ 0) (hz : ∃ i, v i = 0) : GoodPoint D.M (s.pt v) := by
  obtain ⟨σ, ε, hε, hv'⟩ := exists_perm_signs v hv hz
  obtain ⟨g, -, hg⟩ := s.exists_conj σ ε hε
  have hgM : (g : G) ∈ D.M := c.hyp81.1 g.2
  rcases hv' with rfl | rfl
  · have := (s.good_of_mem_plane hN7 hlie hp hpq (v := ![1, 0, 0]) (by decide) rfl).conj hgM
    rwa [hg] at this
  · have := (s.good_of_mem_plane hN7 hlie hp hpq (v := ![1, 1, 0]) (by decide) rfl).conj hgM
    rwa [hg] at this

end SignedLift

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
