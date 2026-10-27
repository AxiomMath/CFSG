module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem b15_W15ElevenFourB_conj_inf_centralizer {V : Subgroup G} {m xr : G}
    (hm : m ∈ Subgroup.normalizer (V : Set G)) :
    V ⊓ centralizer ({m⁻¹ * xr * m} : Set G) =
      conjSubgroup (V ⊓ centralizer ({xr} : Set G)) m := by
  ext s
  rw [Subgroup.mem_inf, mem_conjSubgroup_iff, Subgroup.mem_inf]
  constructor
  · rintro ⟨hsV, hsC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hm s).1 hsV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have hcomm : (m⁻¹ * xr * m) * s = s * (m⁻¹ * xr * m) :=
      hsC (m⁻¹ * xr * m) (Set.mem_singleton _)
    calc xr * (m * s * m⁻¹) = m * ((m⁻¹ * xr * m) * s) * m⁻¹ := by group
      _ = m * (s * (m⁻¹ * xr * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * s * m⁻¹) * xr := by group
  · rintro ⟨hsV, hsC⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hm s).2 hsV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have hcomm : xr * (m * s * m⁻¹) = (m * s * m⁻¹) * xr :=
      hsC xr (Set.mem_singleton _)
    have key : m * ((m⁻¹ * xr * m) * s) * m⁻¹ = m * (s * (m⁻¹ * xr * m)) * m⁻¹ := by
      calc m * ((m⁻¹ * xr * m) * s) * m⁻¹ = xr * (m * s * m⁻¹) := by group
        _ = (m * s * m⁻¹) * xr := hcomm
        _ = m * (s * (m⁻¹ * xr * m)) * m⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel key)

namespace Cfg1511

variable {M V₀ V U S H P Q₀ R : Subgroup G} {p : ℕ}

private theorem b15_W15ElevenFourB_sup_le (c : Cfg1511 M V₀ V U S H P Q₀ p) {g : G}
    (hg : g ∈ centralizer (U : Set G)) {a : G} (ha : a ∈ v1Sub15 V₀ U) :
    U ⊔ v1Sub15 V₀ U ≤ V ⊓ centralizer ({g * a * g⁻¹} : Set G) := by
  refine le_inf (sup_le c.cex.le ((v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le))
    (sup_le ?_ ?_)
  · intro u hu
    have hug : u * g = g * u := Subgroup.mem_centralizer_iff.1 hg u hu
    have hug' : g⁻¹ * u = u * g⁻¹ := by
      calc g⁻¹ * u = g⁻¹ * u * (g * g⁻¹) := by group
        _ = g⁻¹ * (u * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * u) * g⁻¹ := by rw [hug]
        _ = u * g⁻¹ := by group
    have hua : u * a = a * u :=
      B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian (c.cex.le hu)
        (c.cex.hyp.h6.le (v1Sub15_le_left V₀ U ha))
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    calc (g * a * g⁻¹) * u = g * a * (g⁻¹ * u) := by group
      _ = g * a * (u * g⁻¹) := by rw [hug']
      _ = g * (a * u) * g⁻¹ := by group
      _ = g * (u * a) * g⁻¹ := by rw [hua]
      _ = u * (g * a * g⁻¹) := by
            calc g * (u * a) * g⁻¹ = (g * u) * a * g⁻¹ := by group
              _ = (u * g) * a * g⁻¹ := by rw [← hug]
              _ = u * (g * a * g⁻¹) := by group
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact (c.cex.v1Sub15_comm_conj hg hz ha).symm

theorem not_V_le_centralizer_conj
    (c : Cfg1511 M V₀ V U S H P Q₀ p) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M)
    {y : G} (hy : y ∈ v1Sub15 V₀ U) (hy1 : y ≠ 1) :
    ¬ V ≤ centralizer ({g * y * g⁻¹} : Set G) := by
  intro hle
  have hg' : g⁻¹ ∈ centralizer (U : Set G) := (centralizer (U : Set G)).inv_mem hg
  have hgM' : g⁻¹ ∉ M := fun hm => hgM (by simpa using M.inv_mem hm)
  refine (Cex15.not_V_le_conj_M c.inputs c.std c.cex hg' hgM') ?_
  intro z hz
  rw [mem_conjSubgroup_iff]
  have hcomm : (g * y * g⁻¹) * z = z * (g * y * g⁻¹) :=
    Subgroup.mem_centralizer_iff.1 (hle hz) _ (Set.mem_singleton _)
  have hw : g⁻¹ * z * g ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have key : g * (y * (g⁻¹ * z * g)) * g⁻¹ = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by
      calc g * (y * (g⁻¹ * z * g)) * g⁻¹ = (g * y * g⁻¹) * z := by group
        _ = z * (g * y * g⁻¹) := hcomm
        _ = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel key)
  simpa using c.cex.hyp.centralizer_le hy.1 hy1 hw

theorem inf_centralizer_singleton_eq
    (c : Cfg1511 M V₀ V U S H P Q₀ p) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M)
    {y : G} (hy : y ∈ v1Sub15 V₀ U) (hy1 : y ≠ 1) :
    V ⊓ centralizer ({g * y * g⁻¹} : Set G) = U ⊔ v1Sub15 V₀ U := by
  refine le_antisymm ?_ (b15_W15ElevenFourB_sup_le c hg hy)
  intro a ha
  obtain ⟨w, hw, u, hu, hwu⟩ := c.cex.decomp ha.1
  have hUC : U ≤ centralizer ({g * y * g⁻¹} : Set G) :=
    ((le_sup_left : U ≤ U ⊔ v1Sub15 V₀ U).trans
      (b15_W15ElevenFourB_sup_le c hg hy)).trans inf_le_right
  have hV₁C : v1Sub15 V₀ U ≤ centralizer ({g * y * g⁻¹} : Set G) :=
    ((le_sup_right : v1Sub15 V₀ U ≤ U ⊔ v1Sub15 V₀ U).trans
      (b15_W15ElevenFourB_sup_le c hg hy)).trans inf_le_right
  have hwC : w ∈ centralizer ({g * y * g⁻¹} : Set G) := by
    have hw' : w = a * u⁻¹ := by rw [hwu]; group
    rw [hw']
    exact (centralizer ({g * y * g⁻¹} : Set G)).mul_mem ha.2
      ((centralizer ({g * y * g⁻¹} : Set G)).inv_mem (hUC hu))
  set D : Subgroup G := V₀ ⊓ centralizer ({g * y * g⁻¹} : Set G) with hDdef
  have hV₁D : v1Sub15 V₀ U ≤ D := le_inf (v1Sub15_le_left V₀ U) hV₁C
  have hDleV₀ : D ≤ V₀ := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (v1Sub15 V₀ U) D V₀ hV₁D hDleV₀
  have h2 : (v1Sub15 V₀ U).relIndex V₀ = 2 := c.w81.relIndex_eq_two c.std c.cex
  rw [h2] at hmul
  have hdvd : D.relIndex V₀ ∣ 2 := Dvd.intro_left _ hmul
  have hDne : D.relIndex V₀ ≠ 1 := by
    intro h1
    have hV₀D : V₀ ≤ D := Subgroup.relIndex_eq_one.1 h1
    exact c.not_V_le_centralizer_conj hg hgM hy hy1
      (c.cex.sup_eq ▸ sup_le hUC (hV₀D.trans inf_le_right))
  have hD2 : D.relIndex V₀ = 2 := ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hDne
  rw [hD2] at hmul
  have h3 : (v1Sub15 V₀ U).relIndex D = 1 := by omega
  have hDleV₁ : D ≤ v1Sub15 V₀ U := Subgroup.relIndex_eq_one.1 h3
  rw [hwu]
  exact (U ⊔ v1Sub15 V₀ U).mul_mem (Subgroup.mem_sup_right (hDleV₁ ⟨hw, hwC⟩))
    (Subgroup.mem_sup_left hu)

theorem exists_B (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) (hRP : R ≤ P) :
    ∃ B : Subgroup G, B ≤ tSub15 M V₀ V U P ∧ IsElemAbelian 2 B ∧
      Nat.card ↥B = Nat.card ↥(v1Sub15 V₀ U) ∧ ¬ U ≤ centralizer (B : Set G) ∧
      ∀ x ∈ B, x ≠ 1 → V ⊓ centralizer ({x} : Set G) ≤ centralizer (B : Set G) := by
  classical
  obtain ⟨g, hgC, hgM⟩ := SetLike.not_le_iff_exists.1 c.cex.not_le
  obtain ⟨y₀, hy₀ne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (c.cex.v1Sub15_ne_bot c.std)
  set y : G := (y₀ : G) with hydef
  have hy1 : y ∈ v1Sub15 V₀ U := by rw [hydef]; exact y₀.2
  have hyne : y ≠ 1 := by rw [hydef]; exact fun h => hy₀ne (Subtype.ext h)
  have hV₁ne : U ⊔ v1Sub15 V₀ U ≠ V := by
    intro hAV
    apply c.not_V_le_centralizer_conj hgC hgM hy1 hyne
    rw [← hAV, ← c.inf_centralizer_singleton_eq hgC hgM hy1 hyne]
    exact inf_le_right
  have hex : ∃ m₀ ∈ M, ∃ u ∈ U, m₀ * u * m₀⁻¹ ∉ U ⊔ v1Sub15 V₀ U := by
    by_contra hcon
    have hall : ∀ m₀ ∈ M, ∀ u ∈ U, m₀ * u * m₀⁻¹ ∈ U ⊔ v1Sub15 V₀ U := by
      intro m₀ hm₀ u hu
      by_contra h
      exact hcon ⟨m₀, hm₀, u, hu, h⟩
    obtain ⟨u₀, hu₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.cex.ne_bot
    set u : G := (u₀ : G) with hudef
    have huU : u ∈ U := by rw [hudef]; exact u₀.2
    have hune : u ≠ 1 := by rw [hudef]; exact fun h => hu₀ne (Subtype.ext h)
    have huV : u ∈ V := c.cex.le huU
    have huV₀ : u ∉ V₀ := by
      intro h
      have hmem : u ∈ U ⊓ V₀ := ⟨huU, h⟩
      rw [c.cex.inf_eq_bot, Subgroup.mem_bot] at hmem
      exact hune hmem
    have hVA : V ≤ U ⊔ v1Sub15 V₀ U := by
      rw [c.cex.hyp.h6.conjGenerated c.cex.hyp.ne_bot u huV huV₀]
      exact (Subgroup.closure_le (K := U ⊔ v1Sub15 V₀ U)).2 fun x hx => by
        obtain ⟨m₀, hm₀, rfl⟩ := hx
        exact hall m₀ hm₀ u huU
    have hAV : U ⊔ v1Sub15 V₀ U ≤ V :=
      sup_le c.cex.le ((v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le)
    exact hV₁ne (le_antisymm hAV hVA)
  obtain ⟨m₀, hm₀M, u₁, hu₁U, hm₀u₁⟩ := hex
  have hV₁2 : IsPGroup 2 (v1Sub15 V₀ U) :=
    c.cex.hyp.isPGroup.to_le ((v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le)
  set V₂ : Subgroup G := conjSubgroup (v1Sub15 V₀ U) g⁻¹ with hV₂def
  have hV₂C : V₂ ≤ F11.CTilde M V₀ V := by
    intro x hx
    rw [hV₂def, conjSubgroup] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine c.S_le_cTilde (c.cex.pCoreOf_le_S ?_)
    simpa [MulAut.conj_apply, inv_inv] using (conj_mem_pCoreOf_iff hgC a).2 ha.2
  have hV₂2 : IsPGroup 2 V₂ := E3.isPGroup_conjSubgroup hV₁2 g⁻¹
  set B₁ : Subgroup G := conjSubgroup V₂ m₀ with hB₁def
  have hMnormC : M ≤ normalizer (F11.CTilde M V₀ V : Set G) := by
    have hMleV : M ≤ normalizer (V : Set G) := by
      intro m hm
      rw [c.cex.hyp.h6.normalizer_eq]
      exact hm
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).1
      (cTilde_subgroupOf_normal c.cex.hyp.h6.elemAbelian hMleV c.cex.hyp.h6.le_normalizer₀)
  have hB₁C : B₁ ≤ F11.CTilde M V₀ V := by
    intro x hx
    rw [hB₁def, conjSubgroup] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    simpa [MulAut.conj_apply, inv_inv] using
      (Subgroup.mem_normalizer_iff.1 (hMnormC (M.inv_mem hm₀M)) b).1 (hV₂C hb)
  have hB₁2 : IsPGroup 2 B₁ := E3.isPGroup_conjSubgroup hV₂2 m₀
  obtain ⟨d, hdC, hdB₁R⟩ := E3.exists_le_conj_of_isSylowIn hR hB₁C hB₁2
  have hdM : d ∈ M := cTilde_le_M M V₀ V hdC
  have hinvM : d⁻¹ ∈ M := M.inv_mem hdM
  set m : G := m₀ * d⁻¹ with hmdef
  have hmM : m ∈ M := M.mul_mem hm₀M hinvM
  have hVnorm : m ∈ normalizer (V : Set G) := by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact hmM
  have hV₁norm : M ≤ normalizer (v1Sub15 V₀ U : Set G) :=
    Cex15.normal_v1Sub15 c.inputs c.std c.cex
  set B : Subgroup G := conjSubgroup B₁ d⁻¹ with hBdef
  have hB_eq : B = conjSubgroup (v1Sub15 V₀ U) (g⁻¹ * m) := by
    rw [hBdef, hB₁def, hV₂def, hmdef, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
  have hBR : B ≤ R := by
    rw [hBdef]
    calc conjSubgroup B₁ d⁻¹ ≤ conjSubgroup (conjSubgroup R d) d⁻¹ :=
          E3.conjSubgroup_mono_left d⁻¹ hdB₁R
      _ = conjSubgroup R (d * d⁻¹) := conjSubgroup_conjSubgroup R d d⁻¹
      _ = R := by rw [mul_inv_cancel, conjSubgroup_one]
  have hBP : B ≤ P := hBR.trans hRP
  have hBC : B ≤ F11.CTilde M V₀ V := by
    rw [hBdef]
    intro x hx
    rw [conjSubgroup] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    simpa [MulAut.conj_apply, inv_inv] using
      (Subgroup.mem_normalizer_iff.1 (hMnormC hdM) b).1 (hB₁C hb)
  have hBcent : B ≤ centralizer (v1Sub15 V₀ U : Set G) := by
    rw [hB_eq]
    intro b hb
    rw [conjSubgroup] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : m * z * m⁻¹ ∈ v1Sub15 V₀ U :=
      (Subgroup.mem_normalizer_iff.1 (hV₁norm hmM) z).1 hz
    have hcomm : (m * z * m⁻¹) * (g * a * g⁻¹) = (g * a * g⁻¹) * (m * z * m⁻¹) :=
      c.cex.v1Sub15_comm_conj hgC hz' ha
    have key : m * (z * ((g⁻¹ * m)⁻¹ * a * ((g⁻¹ * m)⁻¹)⁻¹)) * m⁻¹ =
        m * (((g⁻¹ * m)⁻¹ * a * ((g⁻¹ * m)⁻¹)⁻¹) * z) * m⁻¹ := by
      calc m * (z * ((g⁻¹ * m)⁻¹ * a * ((g⁻¹ * m)⁻¹)⁻¹)) * m⁻¹
          = (m * z * m⁻¹) * (g * a * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (m * z * m⁻¹) := hcomm
        _ = m * (((g⁻¹ * m)⁻¹ * a * ((g⁻¹ * m)⁻¹)⁻¹) * z) * m⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel key)
  have hV₁elem : IsElemAbelian 2 (v1Sub15 V₀ U) :=
    CFSG.Open.IsElemAbelian.mono c.cex.hyp.elemAbelian₀ (v1Sub15_le_left V₀ U)
  have hBe : IsElemAbelian 2 B := by
    rw [hB_eq]
    exact E3.isElemAbelian_conjSubgroup hV₁elem (g⁻¹ * m)
  have hBcard : Nat.card ↥B = Nat.card ↥(v1Sub15 V₀ U) := by
    rw [hB_eq]
    exact E3.card_conjSubgroup (v1Sub15 V₀ U) (g⁻¹ * m)
  have hBcen : ∀ x ∈ B, x ≠ 1 → V ⊓ centralizer ({x} : Set G) ≤
      centralizer (B : Set G) := by
    intro x hx hx1
    rw [hB_eq] at hx
    rw [conjSubgroup] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have ha1 : a ≠ 1 := by
      intro ha1
      apply hx1
      rw [ha1]
      simp
    have hx'_eq : V ⊓ centralizer ({g * a * g⁻¹} : Set G) = U ⊔ v1Sub15 V₀ U :=
      c.inf_centralizer_singleton_eq hgC hgM ha ha1
    have hx_eq : V ⊓ centralizer ({(g⁻¹ * m)⁻¹ * a * ((g⁻¹ * m)⁻¹)⁻¹} : Set G) =
        conjSubgroup (U ⊔ v1Sub15 V₀ U) m := by
      rw [show (g⁻¹ * m)⁻¹ * a * ((g⁻¹ * m)⁻¹)⁻¹ = m⁻¹ * (g * a * g⁻¹) * m by group,
        b15_W15ElevenFourB_conj_inf_centralizer (hm := hVnorm), hx'_eq]
    rw [hx_eq]
    intro s hs
    rw [mem_conjSubgroup_iff] at hs
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [hB_eq] at hb
    rw [conjSubgroup] at hb
    obtain ⟨a₂, ha₂, rfl⟩ := hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hsA : (g * a₂ * g⁻¹) * (m * s * m⁻¹) = (m * s * m⁻¹) * (g * a₂ * g⁻¹) :=
      Subgroup.mem_centralizer_iff.1
        ((b15_W15ElevenFourB_sup_le c hgC ha₂) hs).2 _ (Set.mem_singleton _)
    have key : m * (s * ((g⁻¹ * m)⁻¹ * a₂ * ((g⁻¹ * m)⁻¹)⁻¹)) * m⁻¹ =
        m * (((g⁻¹ * m)⁻¹ * a₂ * ((g⁻¹ * m)⁻¹)⁻¹) * s) * m⁻¹ := by
      calc m * (s * ((g⁻¹ * m)⁻¹ * a₂ * ((g⁻¹ * m)⁻¹)⁻¹)) * m⁻¹
          = (m * s * m⁻¹) * (g * a₂ * g⁻¹) := by group
        _ = (g * a₂ * g⁻¹) * (m * s * m⁻¹) := hsA.symm
        _ = m * (((g⁻¹ * m)⁻¹ * a₂ * ((g⁻¹ * m)⁻¹)⁻¹) * s) * m⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel key.symm)
  have hnotU : ¬ U ≤ centralizer (B : Set G) := by
    intro hUc
    have hx_eq_A : V ⊓ centralizer ({m⁻¹ * (g * y * g⁻¹) * m} : Set G) =
        conjSubgroup (U ⊔ v1Sub15 V₀ U) m := by
      rw [b15_W15ElevenFourB_conj_inf_centralizer (hm := hVnorm),
        c.inf_centralizer_singleton_eq hgC hgM hy1 hyne]
    have hall : ∀ u ∈ U, m * u * m⁻¹ ∈ U ⊔ v1Sub15 V₀ U := by
      intro u hu
      have hx_mem : m⁻¹ * (g * y * g⁻¹) * m ∈ B := by
        rw [hB_eq, mem_conjSubgroup_iff]
        have hy' : (g⁻¹ * m) * (m⁻¹ * (g * y * g⁻¹) * m) * (g⁻¹ * m)⁻¹ = y := by
          group
        rw [hy']
        exact hy1
      have huCx : u ∈ centralizer ({m⁻¹ * (g * y * g⁻¹) * m} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact Subgroup.mem_centralizer_iff.1 (hUc hu) _ hx_mem
      have hmem : u ∈ V ⊓ centralizer ({m⁻¹ * (g * y * g⁻¹) * m} : Set G) :=
        ⟨c.cex.le hu, huCx⟩
      rw [hx_eq_A, mem_conjSubgroup_iff] at hmem
      exact hmem
    have hd'C : d⁻¹ ∈ F11.CTilde M V₀ V := (F11.CTilde M V₀ V).inv_mem hdC
    have hcomm' : ∀ u ∈ U, m₀ * u * m₀⁻¹ ∈ U ⊔ v1Sub15 V₀ U := by
      intro u hu
      have hmu := hall u hu
      have hw : ⁅d⁻¹, u⁆ ∈ v1Sub15 V₀ U :=
        Cex15.commutator_cTilde_le_v1Sub15 c.inputs c.std c.cex
          (Subgroup.commutator_mem_commutator hd'C (c.cex.le hu))
      have hw' : m₀ * ⁅d⁻¹, u⁆ * m₀⁻¹ ∈ v1Sub15 V₀ U :=
        (Subgroup.mem_normalizer_iff.1 (hV₁norm hm₀M) ⁅d⁻¹, u⁆).1 hw
      have hid : m * u * m⁻¹ = (m₀ * ⁅d⁻¹, u⁆ * m₀⁻¹) * (m₀ * u * m₀⁻¹) := by
        rw [hmdef, commutatorElement_def]
        group
      have hsplit : m₀ * u * m₀⁻¹ = (m₀ * ⁅d⁻¹, u⁆ * m₀⁻¹)⁻¹ * (m * u * m⁻¹) := by
        rw [hid]
        group
      rw [hsplit]
      exact (U ⊔ v1Sub15 V₀ U).mul_mem
        ((U ⊔ v1Sub15 V₀ U).inv_mem (Subgroup.mem_sup_right hw'))
        hmu
    exact hm₀u₁ (hcomm' u₁ hu₁U)
  exact ⟨B, le_tSub15 hBP hBC hBcent, hBe, hBcard, hnotU, hBcen⟩

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
