module

public import CFSG.Quasithin.EmptyFaithful.SzN15Good
public import CFSG.Quasithin.EmptyFaithful.S153DGen3
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.SzN15

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G]

private theorem normalizer_le_normalizer_omegaOneOf {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (omegaOneOf X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ u ∈ omegaOneOf X,
      g * u * g⁻¹ ∈ omegaOneOf X := by
    intro g hg u hu
    unfold omegaOneOf at hu ⊢
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      refine ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hx.1, ?_⟩
      have h2 := hx.2
      rw [conj_pow, h2]
      group
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

private theorem normalizer_le_normalizer_centerOf {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (centerOf H : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (H : Set G), ∀ x ∈ centerOf H, g * x * g⁻¹ ∈ centerOf H := by
    intro g hg x hx
    rw [centerOf, Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxH, hxc⟩ := hx
    refine ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hxH, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxc ⊢
    intro h hh
    have hh' : g⁻¹ * h * g ∈ H := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) h).1 hh
      simpa using this
    have h1 := hxc _ hh'
    calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * h := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer_omegaOneCenterOf' {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (omegaOneCenterOf H : Set G) :=
  normalizer_le_normalizer_omegaOneOf (normalizer_le_normalizer_centerOf hg)

theorem mem_normalizer_sup {L R : Subgroup G} {g : G} (hL : g ∈ Subgroup.normalizer (L : Set G))
    (hR : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer ((L ⊔ R : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (L : Set G), g ∈ Subgroup.normalizer (R : Set G) →
      ∀ u ∈ L ⊔ R, g * u * g⁻¹ ∈ L ⊔ R := by
    intro g hgL hgR u hu
    have hle : L ⊔ R ≤ (L ⊔ R).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 hgL x).1 hx)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 hgR x).1 hx)
    exact hle hu
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hL hR h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hL) (inv_mem hR) _ hh
  simpa [mul_assoc] using this

theorem autOn_le_normalizer {Y L W : Subgroup G} (hYL : Y ≤ Subgroup.normalizer (L : Set G)) :
    autOn Y W ≤ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hYL

theorem conjAct_mem_autOn_of_le {A W : Subgroup G} (hAW : A ≤ Subgroup.normalizer (W : Set G)) {g : G}
    (hg : g ∈ A) : conjAct W ⟨g, hAW hg⟩ ∈ autOn A W :=
  CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨⟨g, hAW hg⟩, hg, rfl⟩

theorem exists_good_parabolic {L S₀ W A : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hS₀ : IsSylowTwoOf S₀ L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hAS : A ≤ Subgroup.normalizer (S₀ : Set G))
    (hgood : GoodCoatom (autOn L W) (autOn S₀ W)) :
    ∃ P : Subgroup G, IsMaxParabolic2 L P ∧ L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P ∧
      A ≤ Subgroup.normalizer (P : Set G) := by
  obtain ⟨Q, hQ, hNQ, hQa⟩ := hgood
  set ρ := S153D.autOnHom hLW with hρ
  have hρs : Function.Surjective ρ := S153D.autOnHom_surjective hLW
  have hker : ∀ k : ↥L, ρ k = 1 → k ∈ Q.comap ρ := fun k hk => by
    rw [Subgroup.mem_comap, hk]
    exact Q.one_mem
  have hBP : L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ (Q.comap ρ).map L.subtype := by
    intro x hx
    refine Subgroup.mem_map.2 ⟨⟨x, hx.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    refine hNQ (ρ ⟨x, hx.1⟩) ?_
    have h1 : conjAct W ⟨x, hLW hx.1⟩ ∈ autOn (L ⊓ Subgroup.normalizer (S₀ : Set G)) W :=
      conjAct_mem_autOn_of_le (A := L ⊓ Subgroup.normalizer (S₀ : Set G))
        (fun y hy => hLW hy.1) hx
    exact autOn_le_normalizer (Y := L ⊓ Subgroup.normalizer (S₀ : Set G)) (L := S₀) (W := W)
      inf_le_right h1
  refine ⟨(Q.comap ρ).map L.subtype, ⟨⟨Subgroup.map_subtype_le _, S₀, hS₀, hBP⟩, ?_, ?_⟩, hBP, ?_⟩
  ·
    intro h
    apply hQ.lt.ne
    rw [eq_top_iff]
    intro q _
    obtain ⟨l, rfl⟩ := hρs q
    have hl : (l : G) ∈ (Q.comap ρ).map L.subtype := by rw [h]; exact l.2
    obtain ⟨l', hl', hll'⟩ := Subgroup.mem_map.1 hl
    have hl'l : l' = l := Subtype.ext hll'
    subst hl'l
    exact hl'
  ·
    intro Q₂ hQ₂ hne hPQ
    have hQ₂L : Q₂ ≤ L := hQ₂.1
    set M : Subgroup ↥L := Q₂.subgroupOf L with hM
    have hcM : Q.comap ρ ≤ M := by
      intro l hl
      exact hPQ (Subgroup.mem_map.2 ⟨l, hl, rfl⟩)
    have hQT : Q ≤ M.map ρ := by
      intro q hq
      obtain ⟨l, rfl⟩ := hρs q
      exact Subgroup.mem_map.2 ⟨l, hcM hq, rfl⟩
    rcases hQ.eq_or_eq hQT le_top with hT | hT
    · have hMle : M ≤ Q.comap ρ := by
        intro m hm
        rw [Subgroup.mem_comap]
        have : ρ m ∈ M.map ρ := Subgroup.mem_map.2 ⟨m, hm, rfl⟩
        rwa [hT] at this
      have hMeq : M = Q.comap ρ := le_antisymm hMle hcM
      rw [← Subgroup.map_subgroupOf_eq_of_le hQ₂L, ← hM, hMeq]
    · exfalso
      apply hne
      refine le_antisymm hQ₂L (fun x hx => ?_)
      have hMtop : M = ⊤ := by
        rw [eq_top_iff]
        intro l _
        have : ρ l ∈ M.map ρ := by rw [hT]; trivial
        obtain ⟨m, hm, hml⟩ := Subgroup.mem_map.1 this
        have hk : m⁻¹ * l ∈ M := hcM (hker _ (by rw [map_mul, map_inv, hml, inv_mul_cancel]))
        have := M.mul_mem hm hk
        rwa [mul_inv_cancel_left] at this
      have : (⟨x, hx⟩ : ↥L) ∈ M := by rw [hMtop]; trivial
      exact this
  ·
    have key : ∀ g ∈ A, ∀ p ∈ (Q.comap ρ).map L.subtype, g * p * g⁻¹ ∈ (Q.comap ρ).map L.subtype := by
      intro g hg p hp
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hp
      have hgL : g * (l : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hAL hg) _).1 l.2
      refine Subgroup.mem_map.2 ⟨⟨g * (l : G) * g⁻¹, hgL⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      set a : MulAut ↥W := conjAct W ⟨g, hAW hg⟩ with ha
      have haA : a ∈ autOn A W := conjAct_mem_autOn_of_le hAW hg
      have haX : a ∈ Subgroup.normalizer (autOn L W : Set (MulAut ↥W)) := autOn_le_normalizer hAL haA
      have haS : a ∈ Subgroup.normalizer (autOn S₀ W : Set (MulAut ↥W)) := autOn_le_normalizer hAS haA
      refine hQa a haX haS (ρ l) (ρ ⟨g * (l : G) * g⁻¹, hgL⟩) ?_ hl
      have e : (⟨g * (l : G) * g⁻¹, hLW hgL⟩ : ↥(Subgroup.normalizer (W : Set G))) =
          ⟨g, hAW hg⟩ * ⟨(l : G), hLW l.2⟩ * ⟨g, hAW hg⟩⁻¹ := rfl
      show conjAct W ⟨g * (l : G) * g⁻¹, hLW hgL⟩ = a * conjAct W ⟨(l : G), hLW l.2⟩ * a⁻¹
      rw [e, map_mul, map_mul, map_inv]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro p
    exact ⟨fun hp => key g hg p hp, fun hp => by
      have := key g⁻¹ (inv_mem hg) _ hp
      simpa [mul_assoc] using this⟩

theorem isPGroup_autOn {R W : Subgroup G} (hRW : R ≤ Subgroup.normalizer (W : Set G))
    (hR : IsPGroup 2 ↥R) : IsPGroup 2 ↥(autOn R W) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hR

theorem autOn_inf_centralizer_eq_bot {L R W : Subgroup G} (hR2 : IsPGroup 2 ↥R)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hYW : L ⊔ R ≤ Subgroup.normalizer (W : Set G))
    (hO2 : pCoreOf 2 (autOn (L ⊔ R) W) = ⊥) :
    autOn R W ⊓ Subgroup.centralizer (autOn L W : Set (MulAut ↥W)) = ⊥ := by
  have hRW : R ≤ Subgroup.normalizer (W : Set G) := le_sup_right.trans hYW
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hYW
  set D : Subgroup (MulAut ↥W) := autOn R W ⊓ Subgroup.centralizer (autOn L W : Set (MulAut ↥W)) with hD
  have hDY : D ≤ autOn (L ⊔ R) W :=
    inf_le_left.trans (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le le_sup_right)
  have hD2 : IsPGroup 2 ↥D := (isPGroup_autOn hRW hR2).to_le inf_le_left
  have hNl : ∀ (l : G) (hl : l ∈ L),
      conjAct W ⟨l, hLW hl⟩ ∈ Subgroup.normalizer (D : Set (MulAut ↥W)) :=
    fun l hl => by
      have hal : conjAct W ⟨l, hLW hl⟩ ∈ autOn L W :=
        CFSG.Quasithin.InternalSec.conjAct_mem_autOn hLW hl
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ a ∈ autOn L W, ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
        intro a ha d hd
        have h1 : a * d = d * a := Subgroup.mem_centralizer_iff.1 hd.2 a ha
        rw [h1, mul_inv_cancel_right]
        exact hd
      intro d
      refine ⟨key _ hal d, fun hd => ?_⟩
      have h2 := key _ ((autOn L W).inv_mem hal) _ hd
      simpa [mul_assoc] using h2
  have hNr : ∀ (r : G) (hr : r ∈ R),
      conjAct W ⟨r, hRW hr⟩ ∈ Subgroup.normalizer (D : Set (MulAut ↥W)) :=
    fun r hr => by
      have har : conjAct W ⟨r, hRW hr⟩ ∈ autOn R W :=
        CFSG.Quasithin.InternalSec.conjAct_mem_autOn hRW hr
      have key : ∀ a ∈ autOn R W, ∀ d ∈ D, a * d * a⁻¹ ∈ D := by
        intro a ha d hd
        refine ⟨(autOn R W).mul_mem ((autOn R W).mul_mem ha hd.1) ((autOn R W).inv_mem ha),
          Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
        have hk' : a⁻¹ * k * a ∈ autOn L W := by
          have := CFSG.Quasithin.InternalSec.autOn_normal_of (U := W) (Y := R) (L := L) hRL
            a⁻¹ ((autOn R W).inv_mem ha) k hk
          simpa using this
        have h1 : (a⁻¹ * k * a) * d = d * (a⁻¹ * k * a) := Subgroup.mem_centralizer_iff.1 hd.2 _ hk'
        calc k * (a * d * a⁻¹) = a * ((a⁻¹ * k * a) * d) * a⁻¹ := by group
          _ = a * (d * (a⁻¹ * k * a)) * a⁻¹ := by rw [h1]
          _ = (a * d * a⁻¹) * k := by group
      rw [Subgroup.mem_normalizer_iff]
      intro d
      refine ⟨key _ har d, fun hd => ?_⟩
      have h2 := key _ ((autOn R W).inv_mem har) _ hd
      simpa [mul_assoc] using h2
  have hDn : autOn (L ⊔ R) W ≤ Subgroup.normalizer (D : Set (MulAut ↥W)) := by
    intro y hy
    obtain ⟨g, hgY, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.1 hy
    obtain ⟨l, hl, r, hr, hlr⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hRL).1 hgY
    have hge : g = ⟨l, hLW hl⟩ * ⟨r, hRW hr⟩ := Subtype.ext hlr
    rw [hge, map_mul]
    exact Subgroup.mul_mem _ (hNl l hl) (hNr r hr)
  have hle : D ≤ pCoreOf 2 (autOn (L ⊔ R) W) := le_pCoreOf_of_le_normalizer 2 hDY hDn hD2
  rw [hO2] at hle
  exact le_bot_iff.1 hle

end CFSG.Quasithin.SzN15
