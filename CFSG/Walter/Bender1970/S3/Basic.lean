module

public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.Bender1970.S2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerConjugate

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

section Membership

variable {s : G} {H : Subgroup G}

theorem isCoatom_of_mem_benderM (hH : H ∈ benderM s) : IsCoatom H := hH.1

theorem centralizer_le_of_mem_benderM (hH : H ∈ benderM s) :
    Subgroup.centralizer ({s} : Set G) ≤ H := hH.2.1

theorem ne_top_of_mem_benderM (hH : H ∈ benderM s) : H ≠ ⊤ := hH.1.1

theorem mem_of_mem_benderM (hH : H ∈ benderM s) : s ∈ H :=
  hH.2.1 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

end Membership

section Conj

omit [Finite G] in
theorem map_conj_centralizer_singleton (g s : G) :
    (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * s * g⁻¹} : Set G) := by
  rw [map_centralizer_singleton_mulEquiv, MulAut.conj_apply]

omit [Finite G] in
theorem isCoatom_map_conj {H : Subgroup G} (g : G) (hH : IsCoatom H) :
    IsCoatom (H.map (MulAut.conj g).toMonoidHom) :=
  (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) H).mpr hH

omit [Finite G] in
theorem isCoatom_of_map_conj {H : Subgroup G} (g : G)
    (hH : IsCoatom (H.map (MulAut.conj g).toMonoidHom)) : IsCoatom H :=
  (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) H).mp hH

omit [Finite G] in
theorem map_conj_le_map_conj_iff {A B : Subgroup G} (g : G) :
    A.map (MulAut.conj g).toMonoidHom ≤ B.map (MulAut.conj g).toMonoidHom ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

omit [Finite G] in
theorem map_conj_map_conj_inv (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A
  ext x
  simp [mul_assoc]

omit [Finite G] in
theorem map_conj_inv_map_conj (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  simpa using map_conj_map_conj_inv g⁻¹ A

omit [Finite G] in
theorem map_conj_eq_self_of_mem {A : Subgroup G} {g : G} (hg : g ∈ A) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact A.mul_mem (A.mul_mem hg hy) (A.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, A.mul_mem (A.mul_mem (A.inv_mem hg) hx) hg, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem qCoreOf_map_conj_inf (g s : G) (H : Subgroup G) (p : ℕ) :
    qCoreOf (H.map (MulAut.conj g).toMonoidHom) p ⊓
        Subgroup.centralizer ({g * s * g⁻¹} : Set G) =
      (qCoreOf H p ⊓ Subgroup.centralizer ({s} : Set G)).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_centralizer_singleton]
  exact congrArg (· ⊓ _) (qCoreOf_conjugateSubgroup H g p)

theorem HasFixedPointFreeCore.map_conj {s : G} {H : Subgroup G} (g : G)
    (h : HasFixedPointFreeCore s H) :
    HasFixedPointFreeCore (g * s * g⁻¹) (H.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨p, hp, hne, hfix⟩ := h
  refine ⟨p, hp, ?_, ?_⟩
  · have h1 : qCoreOf (H.conjBy g) p = (qCoreOf H p).map (MulAut.conj g).toMonoidHom :=
      qCoreOf_conjugateSubgroup H g p
    change qCoreOf (H.conjBy g) p ≠ ⊥
    rw [h1, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
    exact hne
  · rw [qCoreOf_map_conj_inf, hfix, Subgroup.map_bot]

theorem card_componentLayerOf_map_conj (g : G) (H : Subgroup G) :
    Nat.card (componentLayerOf (H.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (componentLayerOf H) := by
  change Nat.card (componentLayerOf (conjugateSubgroup H g)) = _
  rw [componentLayerOf_conjugateSubgroup, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem map_conj_mem_benderM {s : G} {H : Subgroup G} (g : G) (hH : H ∈ benderM s) :
    H.map (MulAut.conj g).toMonoidHom ∈ benderM (g * s * g⁻¹) := by
  obtain ⟨hco, hC, hcase⟩ := hH
  refine ⟨isCoatom_map_conj g hco, ?_, ?_⟩
  · rw [← map_conj_centralizer_singleton]
    exact Subgroup.map_mono hC
  rcases hcase with hfp | ⟨hnone, hmax⟩
  · exact Or.inl (hfp.map_conj g)
  · refine Or.inr ⟨fun K hK hCK hKfp => ?_, fun K hK hCK => ?_⟩
    · have hK' := isCoatom_map_conj g⁻¹ hK
      have hCK' : Subgroup.centralizer ({s} : Set G) ≤ K.map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [← map_conj_le_map_conj_iff g, map_conj_inv_map_conj, map_conj_centralizer_singleton]
        exact hCK
      have hfp' := hKfp.map_conj g⁻¹
      have hs : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
      rw [hs] at hfp'
      exact hnone _ hK' hCK' hfp'
    · have hK' := isCoatom_map_conj g⁻¹ hK
      have hCK' : Subgroup.centralizer ({s} : Set G) ≤ K.map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [← map_conj_le_map_conj_iff g, map_conj_inv_map_conj, map_conj_centralizer_singleton]
        exact hCK
      have h1 := hmax _ hK' hCK'
      rw [card_componentLayerOf_map_conj] at h1
      rw [card_componentLayerOf_map_conj]
      exact h1

theorem benderM_conj (g s : G) :
    benderM (g * s * g⁻¹) = (fun H : Subgroup G => H.map (MulAut.conj g).toMonoidHom) ''
      benderM s := by
  ext K
  constructor
  · intro hK
    refine ⟨K.map (MulAut.conj g⁻¹).toMonoidHom, ?_, map_conj_inv_map_conj g K⟩
    have h := map_conj_mem_benderM g⁻¹ hK
    have hs : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
    rwa [hs] at h
  · rintro ⟨H, hH, rfl⟩
    exact map_conj_mem_benderM g hH

theorem benderM_conj_eq_singleton {s : G} {H : Subgroup G} (g : G)
    (h : benderM s = {H}) :
    benderM (g * s * g⁻¹) = {H.map (MulAut.conj g).toMonoidHom} := by
  rw [benderM_conj, h, Set.image_singleton]

end Conj

namespace BenderCounterexample

variable (hG : BenderCounterexample G)
include hG

theorem nontrivial : Nontrivial G := hG.isSimpleGroup.toNontrivial

theorem bot_not_isCoatom : ¬ IsCoatom (⊥ : Subgroup G) := by
  intro hbot
  obtain ⟨a, b, hab⟩ := hG.nonabelian
  have hcyc : ∀ x : G, x ≠ 1 → Subgroup.zpowers x = ⊤ := by
    intro x hx
    refine (hbot.lt_iff).mp (bot_lt_iff_ne_bot.mpr ?_)
    rwa [Ne, Subgroup.zpowers_eq_bot]
  by_cases ha : a = 1
  · exact hab (by rw [ha, one_mul, mul_one])
  have hb : b ∈ Subgroup.zpowers a := by rw [hcyc a ha]; exact Subgroup.mem_top b
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact hab (by simpa using zpow_mul_comm a 1 k)

theorem center_eq_bot : Subgroup.center G = ⊥ := by
  have := hG.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hG.nonabelian
    have hb : b ∈ Subgroup.center G := h ▸ Subgroup.mem_top b
    exact hab ((Subgroup.mem_center_iff.mp hb a))

theorem centralizer_ne_top {s : G} (hs : s ≠ 1) :
    Subgroup.centralizer ({s} : Set G) ≠ ⊤ := by
  intro h
  apply hs
  have hz : s ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({s} : Set G) := h ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [hG.center_eq_bot] at hz
  exact Subgroup.mem_bot.mp hz

theorem normalizer_eq_of_isCoatom {H : Subgroup G} (hH : IsCoatom H) :
    Subgroup.normalizer (H : Set G) = H := by
  have := hG.isSimpleGroup
  rcases (hH.le_iff).mp (Subgroup.le_normalizer (H := H)) with h | h
  · exfalso
    have hn : H.Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h' | h'
    · exact hG.bot_not_isCoatom (h' ▸ hH)
    · exact hH.1 h'
  · exact h

theorem mem_of_map_conj_eq {H : Subgroup G} (hH : IsCoatom H) {g : G}
    (hg : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ H := by
  rw [← hG.normalizer_eq_of_isCoatom hH, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [hg] at h1
  · intro hx
    rw [← hg] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [mul_assoc] using this
    rwa [← this]

theorem isAStar_of_isCoatom {H : Subgroup G} (hH : IsCoatom H) : IsAStar H :=
  hG.isAStar H hH.1

theorem benderM_nonempty {s : G} (hs : s ≠ 1) : (benderM s).Nonempty := by
  classical
  set C := Subgroup.centralizer ({s} : Set G)
  set 𝒦 : Set (Subgroup G) := {K | IsCoatom K ∧ C ≤ K}
  have hne : 𝒦.Nonempty := by
    rcases eq_top_or_exists_le_coatom C with h | ⟨K, hK, hCK⟩
    · exact absurd h (hG.centralizer_ne_top hs)
    · exact ⟨K, hK, hCK⟩
  by_cases hfp : ∃ K : Subgroup G, IsCoatom K ∧ C ≤ K ∧ HasFixedPointFreeCore s K
  · obtain ⟨K, hK, hCK, hKfp⟩ := hfp
    exact ⟨K, hK, hCK, Or.inl hKfp⟩
  · push Not at hfp
    obtain ⟨K, ⟨hK, hCK⟩, hmax⟩ := Set.exists_max_image 𝒦
      (fun K => Nat.card (componentLayerOf K)) (Set.toFinite 𝒦) hne
    exact ⟨K, hK, hCK, Or.inr ⟨fun K' hK' hCK' => hfp K' hK' hCK',
      fun K' hK' hCK' => hmax K' ⟨hK', hCK'⟩⟩⟩

theorem sylow_le_centralizer (T : Sylow 2 G) {t : G} (htT : t ∈ (T : Subgroup G)) :
    (T : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hG.hasAbelianSylowTwo T
  exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨t, htT⟩)

theorem sylow_le_of_mem_benderM (T : Sylow 2 G) {t : G} (htT : t ∈ (T : Subgroup G))
    {H : Subgroup G} (hH : H ∈ benderM t) : (T : Subgroup G) ≤ H :=
  (hG.sylow_le_centralizer T htT).trans (centralizer_le_of_mem_benderM hH)

end BenderCounterexample

end CFSG.Walter
