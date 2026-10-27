module

public import CFSG.Quasithin.Vol2.Ch10SecD33F
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem map_pCore_mulEquiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    (CFSG.pCore 2 X).map (e : X →* Y) = CFSG.pCore 2 Y := by
  exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e

@[expose] noncomputable def barAct (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) where
  toFun g := QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K) (conjAct K g)
    (map_pCore_mulEquiv' (conjAct K g))
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w => rw [QuotientGroup.congr_mk, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

omit [Finite G] in
theorem barAct_mk (K : Subgroup G) (g : Subgroup.normalizer (K : Set G)) (w : ↥K) :
    barAct K g (QuotientGroup.mk w) = QuotientGroup.mk (conjAct K g w) :=
  QuotientGroup.congr_mk _ _ _ (map_pCore_mulEquiv' _) w

@[expose] noncomputable def barCent (K : Subgroup G) : Subgroup G := (barAct K).ker.map
  (Subgroup.normalizer (K : Set G)).subtype

omit [Finite G] in
theorem mem_barCent_iff_barAct {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ barCent K ↔ barAct K ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨⟨g', hg'⟩, hk, rfl⟩
    exact MonoidHom.mem_ker.mp hk
  · intro h
    exact ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr h, rfl⟩

omit [Finite G] in
theorem mem_barCent_iff {K : Subgroup G} {g : G} :
    g ∈ barCent K ↔ g ∈ Subgroup.normalizer (K : Set G) ∧
      ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have key : ∀ (hg : g ∈ Subgroup.normalizer (K : Set G)) (k : ↥K),
      (barAct K ⟨g, hg⟩ (QuotientGroup.mk k) = QuotientGroup.mk k ↔
        g * k * g⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 K) := by
    intro hg k
    rw [barAct_mk, QuotientGroup.eq]
    have hc : ((conjAct K ⟨g, hg⟩ k)⁻¹ * k : ↥K) =
        ⟨(g * k * g⁻¹)⁻¹ * k, K.mul_mem (K.inv_mem ((Subgroup.mem_normalizer_iff.mp hg k).mp
          k.2)) k.2⟩ := rfl
    rw [hc]
    have hN := mem_normalizer_pCoreOf (Subgroup.le_normalizer k.2)
    have hN' := mem_normalizer_pCoreOf (Subgroup.le_normalizer (K.inv_mem k.2))
    constructor
    · intro h
      have h1 : (g * k * g⁻¹)⁻¹ * k ∈ pCoreOf 2 K := ⟨_, h, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp ((pCoreOf 2 K).inv_mem h1)
      have e : (k : G) * ((g * k * g⁻¹)⁻¹ * k)⁻¹ * (k : G)⁻¹ = g * k * g⁻¹ * (k : G)⁻¹ := by
        group
      rwa [e] at h2
    · intro h
      have h2 := (Subgroup.mem_normalizer_iff.mp hN' _).mp ((pCoreOf 2 K).inv_mem h)
      have e : (k : G)⁻¹ * (g * k * g⁻¹ * (k : G)⁻¹)⁻¹ * (k : G)⁻¹⁻¹ =
          (g * k * g⁻¹)⁻¹ * k := by group
      rw [e] at h2
      obtain ⟨y, hy, hye⟩ := h2
      have : y = ⟨(g * k * g⁻¹)⁻¹ * k, K.mul_mem (K.inv_mem ((Subgroup.mem_normalizer_iff.mp
          hg k).mp k.2)) k.2⟩ := Subtype.ext hye
      rw [← this]
      exact hy
  constructor
  · rintro ⟨⟨g', hg⟩, hker, rfl⟩
    refine ⟨hg, fun k hk => ?_⟩
    have h1 := congrArg (fun φ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => φ (QuotientGroup.mk ⟨k, hk⟩))
      (MonoidHom.mem_ker.mp hker)
    simp only [MulAut.one_apply] at h1
    exact (key hg ⟨k, hk⟩).mp h1
  · rintro ⟨hg, hk⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [MulAut.one_apply]
      exact (key hg w).mpr (hk w w.2)

theorem barCent_conjugate (K : Subgroup G) (s : G) :
    barCent (CFSG.conjugate K s) = CFSG.conjugate (barCent K) s := by
  have hN : ∀ x : G, x ∈ Subgroup.normalizer ((CFSG.conjugate K s : Subgroup G) : Set G) ↔
      s * x * s⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    intro x
    rw [← mem_conjSubgroup_iff]
    have := E3.conjSubgroup_normalizer K s
    exact ⟨fun h => this ▸ h, fun h => this.symm ▸ h⟩
  ext x
  rw [SecA.mem_conjugate_iff, mem_barCent_iff, mem_barCent_iff, SecA.pCoreOf_conjugate, hN]
  refine and_congr_right fun _ => ⟨fun hx k hk => ?_, fun hx k hk => ?_⟩
  · have hk' : s⁻¹ * k * s ∈ CFSG.conjugate K s := by
      rw [SecA.mem_conjugate_iff]
      have e : s * (s⁻¹ * k * s) * s⁻¹ = k := by group
      rw [e]
      exact hk
    have h1 := hx _ hk'
    rw [SecA.mem_conjugate_iff] at h1
    have e : s * (x * (s⁻¹ * k * s) * x⁻¹ * (s⁻¹ * k * s)⁻¹) * s⁻¹ =
        s * x * s⁻¹ * k * (s * x * s⁻¹)⁻¹ * k⁻¹ := by group
    rwa [e] at h1
  · rw [SecA.mem_conjugate_iff] at hk ⊢
    have h1 := hx _ hk
    have e : s * x * s⁻¹ * (s * k * s⁻¹) * (s * x * s⁻¹)⁻¹ * (s * k * s⁻¹)⁻¹ =
        s * (x * k * x⁻¹ * k⁻¹) * s⁻¹ := by group
    rwa [e] at h1

omit [Finite G] in
theorem map_barSub_barAct {K H : Subgroup G} {g : G} (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) :
    (barSub K (H ⊓ K)).map (barAct K ⟨g, hgK⟩ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).toMonoidHom =
      barSub K (H ⊓ K) := by
  have hle : ∀ (g : G) (hgK : g ∈ Subgroup.normalizer (K : Set G)),
      g ∈ Subgroup.normalizer (H : Set G) →
      (barSub K (H ⊓ K)).map (barAct K ⟨g, hgK⟩ : MulAut _).toMonoidHom ≤ barSub K (H ⊓ K) := by
    rintro g hgK hgH _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨conjAct K ⟨g, hgK⟩ w, ?_, ?_⟩
    · have hw' := Subgroup.mem_subgroupOf.mp hw
      exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgH _).mp hw'.1,
        (Subgroup.mem_normalizer_iff.mp hgK _).mp hw'.2⟩
    · change QuotientGroup.mk' _ (conjAct K ⟨g, hgK⟩ w) =
        barAct K ⟨g, hgK⟩ (QuotientGroup.mk' _ w)
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, barAct_mk]
  refine le_antisymm (hle g hgK hgH) ?_
  intro x hx
  have h1 := hle g⁻¹ ((Subgroup.normalizer _).inv_mem hgK) ((Subgroup.normalizer _).inv_mem hgH)
    ⟨x, hx, rfl⟩
  refine ⟨_, h1, ?_⟩
  change barAct K ⟨g, hgK⟩ (barAct K ⟨g⁻¹, _⟩ x) = x
  rw [← MulAut.mul_apply, ← map_mul]
  have : (⟨g, hgK⟩ * ⟨g⁻¹, (Subgroup.normalizer _).inv_mem hgK⟩ :
      Subgroup.normalizer (K : Set G)) = 1 := Subtype.ext (mul_inv_cancel g)
  rw [this, map_one, MulAut.one_apply]

end CFSG.Quasithin.Vol2.Ch10.SecD
