module

public import CFSG.RankThree.GF2n.Parrott.ActionZ
public import CFSG.RankThree.GF2n.Parrott.CentralizerV
public import CFSG.GroupTheory.ExtraspecialCommutatorCentralizer
public import CFSG.GroupTheory.OddInvariantComplement

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mul_mul_inv_eq_of_conjZ_eq_one {ℓ : ↥(H z)} (hℓ : conjZ z ℓ = 1) {t : G}
    (ht : t ∈ centerIn (J z)) : (ℓ : G) * t * (ℓ : G)⁻¹ = t := by
  have h1 := congrArg (fun α : MulAut (centerIn (J z)) => ((α ⟨t, ht⟩ : centerIn (J z)) : G)) hℓ
  simpa [conjZ_apply_coe] using h1

theorem exists_stable_extraspecial_complement (h : Tim79a.ParrottHyp z) (L : Subgroup ↥(H z))
    (hL : Odd (Nat.card L)) (hLZ : ∀ ℓ ∈ L, conjZ z ℓ = 1) :
    ∃ T F' : Subgroup G, Nat.card T = 2 ∧ T ≤ centerIn (J z) ∧ T ⊓ F' = ⊥ ∧ T ⊔ F' = J z ∧
      IsExtraspecial2 F' ∧ ⁅F', F'⁆ = Subgroup.zpowers z ∧
      ∀ ℓ ∈ L, ∀ f ∈ F', (ℓ : G) * f * (ℓ : G)⁻¹ ∈ F' := by
  obtain ⟨T, F, hTcard, -, -, hdisj, hcomm, hsup⟩ := exists_decomposition h
  have hTJ : T ≤ J z := hsup ▸ le_sup_left
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' := fun t ht t' ht' =>
    CFSG.commute_of_mem_of_isMulCommutative (CFSG.isMulCommutative_of_card_two T hTcard) ht ht'
  have hTcentral : ∀ t ∈ T, ∀ j ∈ J z, Commute t j := by
    intro t ht j hj
    rw [← hsup] at hj
    obtain ⟨t', ht', f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hj
    exact (hTT t ht t' ht').mul_right (hcomm t ht f hf)
  have hTcenter : T ≤ centerIn (J z) := fun t ht =>
    ⟨hTJ ht, Subgroup.mem_centralizer_iff.mpr fun j hj => (hTcentral t ht j hj).symm.eq⟩
  set L' : Subgroup G := L.map (H z).subtype with hL'
  have hL'odd : Odd (Nat.card L') := by
    rw [hL', Subgroup.card_map_of_injective (H z).subtype_injective]
    exact hL
  have hLJ : ∀ ℓ ∈ L', ∀ j ∈ J z, ℓ * j * ℓ⁻¹ ∈ J z := by
    rintro _ ⟨ℓ, hℓ, rfl⟩ j hj
    have hjH : j ∈ H z := J_le_H hj
    have h1 := (J_subgroupOf_normal z).conj_mem ⟨j, hjH⟩ (Subgroup.mem_subgroupOf.mpr hj) ℓ
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hLT : ∀ ℓ ∈ L', ∀ t ∈ T, ℓ * t * ℓ⁻¹ = t := by
    rintro _ ⟨ℓ, hℓ, rfl⟩ t ht
    exact mul_mul_inv_eq_of_conjZ_eq_one (hLZ ℓ hℓ) (hTcenter ht)
  obtain ⟨F', hF'J, hTF', hsup', hstab⟩ :=
    CFSG.GroupTheory.exists_invariant_complement_of_odd hTcard hdisj hsup hcomm hL'odd hLJ hLT
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm', -, -⟩ := h
    simpa [J, H] using hcomm'
  have hTF'c : ∀ t ∈ T, ∀ f ∈ F', Commute t f := fun t ht f hf => hTcentral t ht f (hF'J hf)
  have hFF : ⁅F', F'⁆ = Subgroup.zpowers z := by
    refine le_antisymm (hJcomm ▸ Subgroup.commutator_mono hF'J hF'J) ?_
    rw [← hJcomm, ← hsup']
    exact CFSG.commutator_sup_le_commutator_right hTT hTF'c
  have hzF' : z ∈ F' :=
    Subgroup.commutator_le_self F' (hFF ▸ Subgroup.mem_zpowers z)
  have hzpF' : Subgroup.zpowers z ≤ F' := Subgroup.zpowers_le.mpr hzF'
  have hZ : (Subgroup.center F').map F'.subtype = Subgroup.zpowers z := by
    rw [CFSG.center_map_subtype_eq_inf_centralizer]
    have hzcent : z ∈ Subgroup.centralizer (F' : Set G) :=
      Subgroup.centralizer_le hF'J (z_centralizes_J h)
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hzF', hzcent⟩)
    rintro c ⟨hcF', hcc⟩
    have hcJ : c ∈ centerIn (J z) := by
      refine ⟨hF'J hcF', Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
      rw [← hsup'] at hj
      obtain ⟨t, ht, f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hTF'c).mp hj
      have h1 : f * c = c * f := Subgroup.mem_centralizer_iff.mp hcc f hf
      have h2 : t * c = c * t := (hTcentral t ht c (hF'J hcF')).eq
      calc t * f * c = t * (f * c) := by rw [mul_assoc]
        _ = t * (c * f) := by rw [h1]
        _ = (t * c) * f := by rw [mul_assoc]
        _ = (c * t) * f := by rw [h2]
        _ = c * (t * f) := by rw [mul_assoc]
    have hcard4 : Nat.card (centerIn (J z)) = 4 := card_centerIn_J h
    have hzcenter : Subgroup.zpowers z ≤ centerIn (J z) :=
      Subgroup.zpowers_le.mpr ⟨z_mem_J h, z_centralizes_J h⟩
    have hTz : ∀ t ∈ T, ∀ a ∈ Subgroup.zpowers z, Commute t a := fun t ht a ha =>
      hTcentral t ht a (hF'J (hzpF' ha))
    have hdisjz : T ⊓ Subgroup.zpowers z = ⊥ := by
      rw [eq_bot_iff, ← hTF']
      exact inf_le_inf_left T hzpF'
    have hcardsup : Nat.card (T ⊔ Subgroup.zpowers z : Subgroup G) = 4 := by
      rw [CFSG.card_sup_eq_mul_of_commute T _ hTz hdisjz, hTcard, Nat.card_zpowers, h.1]
    have hsupcenter : T ⊔ Subgroup.zpowers z = centerIn (J z) :=
      Subgroup.eq_of_le_of_card_ge (sup_le hTcenter hzcenter) (by rw [hcard4, hcardsup])
    rw [← hsupcenter] at hcJ
    obtain ⟨t, ht, a, ha, rfl⟩ := (CFSG.mem_sup_of_commute hTz).mp hcJ
    have htF' : t ∈ F' := by
      have := F'.mul_mem hcF' (F'.inv_mem (hzpF' ha))
      simpa using this
    have ht1 : t = 1 := by
      have : t ∈ T ⊓ F' := ⟨ht, htF'⟩
      rw [hTF'] at this
      exact this
    rw [ht1, one_mul]
    exact ha
  refine ⟨T, F', hTcard, hTcenter, hTF', hsup', ⟨(isPGroup_J h).to_le hF'J, hFF.trans hZ.symm, ?_⟩,
    hFF, ?_⟩
  · rw [hFF, Nat.card_zpowers, h.1]
  · rintro ℓ hℓ f hf
    exact hstab (ℓ : G) ⟨ℓ, hℓ, rfl⟩ f hf

omit [Finite G] in
private theorem mem_normalizer_of_forall_mem {V M : Subgroup G}
    (hVn : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V) {k : G} (hk : k ∈ M) :
    k ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => hVn k hk v hv, fun hv => ?_⟩
  have := hVn k⁻¹ (M.inv_mem hk) _ hv
  rwa [show k⁻¹ * (k * v * k⁻¹) * k⁻¹⁻¹ = v by group] at this

theorem exists_complement_commutator (h : Tim79a.ParrottHyp z) (L : Subgroup ↥(H z))
    (hL : Odd (Nat.card L)) (hLZ : ∀ ℓ ∈ L, conjZ z ℓ = 1) :
    ∃ F' : Subgroup G, F' ≤ J z ∧ ∀ σ ∈ L, orderOf σ = 3 → conjV h σ ≠ 1 →
      ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ =
          F' ⊓ Subgroup.centralizer
            ((F' ⊓ Subgroup.centralizer ({(σ : G)} : Set G) : Subgroup G) : Set G) ∧
        z ∈ ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ := by
  obtain ⟨T, F', hTcard, hTcenter, hTF', hsup', hF'e, hFF, hstab⟩ :=
    exists_stable_extraspecial_complement h L hL hLZ
  have hF'J : F' ≤ J z := hsup' ▸ le_sup_right
  have hTcentral : ∀ t ∈ T, ∀ j ∈ J z, Commute t j := fun t ht j hj =>
    (Subgroup.mem_centralizer_iff.mp (hTcenter ht).2 j hj).symm
  have hTF'c : ∀ t ∈ T, ∀ f ∈ F', Commute t f := fun t ht f hf => hTcentral t ht f (hF'J hf)
  refine ⟨F', hF'J, fun σ hσL hσ hVσ => ?_⟩
  set P : Subgroup G := (Subgroup.zpowers σ).map (H z).subtype with hP
  have hzσ : Subgroup.zpowers σ ≤ L := Subgroup.zpowers_le.mpr hσL
  have hPcard : Nat.card P = 3 := by
    rw [hP, Subgroup.card_map_of_injective (H z).subtype_injective, Nat.card_zpowers, hσ]
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by rw [hPcard, pow_one])
  have hPstab : ∀ x ∈ P, ∀ f ∈ F', x * f * x⁻¹ ∈ F' := by
    rintro _ ⟨m, hm, rfl⟩ f hf
    exact hstab m (hzσ hm) f hf
  have hNP : P ≤ Subgroup.normalizer (F' : Set G) := fun x hx =>
    mem_normalizer_of_forall_mem hPstab hx
  have hPT : ∀ x ∈ P, ∀ t ∈ T, x * t * x⁻¹ = t := by
    rintro _ ⟨m, hm, rfl⟩ t ht
    exact mul_mul_inv_eq_of_conjZ_eq_one (hLZ m (hzσ hm)) (hTcenter ht)
  have hσP : (σ : G) ∈ P := ⟨σ, Subgroup.mem_zpowers σ, rfl⟩
  have hnot : ¬ P ≤ Subgroup.centralizer (F' : Set G) := by
    intro hPc
    apply hVσ
    have hσc : ∀ j ∈ J z, (σ : G) * j = j * (σ : G) := by
      intro j hj
      rw [← hsup'] at hj
      obtain ⟨t, ht, f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hTF'c).mp hj
      have h1 : (σ : G) * t = t * (σ : G) := by
        have := hPT σ hσP t ht
        calc (σ : G) * t = (σ : G) * t * (σ : G)⁻¹ * (σ : G) := by group
          _ = t * (σ : G) := by rw [this]
      have h2 : (σ : G) * f = f * (σ : G) :=
        (Subgroup.mem_centralizer_iff.mp (hPc hσP) f hf).symm
      calc (σ : G) * (t * f) = ((σ : G) * t) * f := by rw [mul_assoc]
        _ = (t * (σ : G)) * f := by rw [h1]
        _ = t * ((σ : G) * f) := by rw [mul_assoc]
        _ = t * (f * (σ : G)) := by rw [h2]
        _ = (t * f) * (σ : G) := by rw [mul_assoc]
    refine MulEquiv.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
    rw [conjV_mk]
    change QuotientV.pi z (conjJ' z σ x) = QuotientV.pi z x
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have := hσc x x.2
    calc (σ : G) * x * (σ : G)⁻¹ = x * (σ : G) * (σ : G)⁻¹ := by rw [this]
      _ = x := by group
  obtain ⟨hA1, hA2⟩ := CFSG.GroupTheory.commutator_eq_inf_centralizer_inf_centralizer (p := 3)
    Nat.prime_three (by norm_num) hF'e hPp hNP hnot
  have hcentP : F' ⊓ Subgroup.centralizer (P : Set G) =
      F' ⊓ Subgroup.centralizer ({(σ : G)} : Set G) := by
    ext f
    simp only [Subgroup.mem_inf]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hf
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hf σ hσP).symm
    · intro hf
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      obtain ⟨m, hm, rfl⟩ := hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
      have hc : Commute f (σ : G) := Subgroup.mem_centralizer_singleton_iff.mp hf
      have := (hc.zpow_right k).eq
      simpa using this.symm
  have hPJ : ⁅P, J z⁆ = ⁅P, F'⁆ := by
    refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl hF'J)
    rw [Subgroup.commutator_le]
    intro x hx j hj
    rw [← hsup'] at hj
    obtain ⟨t, ht, f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hTF'c).mp hj
    have hxt : x * t * x⁻¹ = t := hPT x hx t ht
    have hxf : x * f * x⁻¹ ∈ F' := hPstab x hx f hf
    have hxt' : x * t = t * x := by
      calc x * t = x * t * x⁻¹ * x := by group
        _ = t * x := by rw [hxt]
    have hy : x * f * x⁻¹ * f⁻¹ ∈ J z := hF'J (F'.mul_mem hxf (F'.inv_mem hf))
    have hty : t * (x * f * x⁻¹ * f⁻¹) = (x * f * x⁻¹ * f⁻¹) * t := (hTcentral t ht _ hy).eq
    have e : ⁅x, t * f⁆ = ⁅x, f⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc x * (t * f) * x⁻¹ * (t * f)⁻¹ = (x * t) * f * x⁻¹ * f⁻¹ * t⁻¹ := by group
        _ = t * x * f * x⁻¹ * f⁻¹ * t⁻¹ := by rw [hxt']
        _ = (t * (x * f * x⁻¹ * f⁻¹)) * t⁻¹ := by group
        _ = ((x * f * x⁻¹ * f⁻¹) * t) * t⁻¹ := by rw [hty]
        _ = x * f * x⁻¹ * f⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator hx hf
  have hzmem : z ∈ (Subgroup.center F').map F'.subtype := by
    have : (Subgroup.center F').map F'.subtype = Subgroup.zpowers z := hF'e.2.1.symm.trans hFF
    rw [this]
    exact Subgroup.mem_zpowers z
  refine ⟨?_, ?_⟩
  · rw [hPJ, hA1, hcentP]
  · rw [hPJ]
    exact hA2 hzmem

theorem inf_centralizer_eq_of_centralizerJ_eq {σ τ : ↥(H z)}
    (hK : centralizerJ σ = centralizerJ τ) {F : Subgroup G} (hFJ : F ≤ J z) :
    F ⊓ Subgroup.centralizer ({(σ : G)} : Set G) =
      F ⊓ Subgroup.centralizer ({(τ : G)} : Set G) := by
  ext f
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hf => ?_
  have := SetLike.ext_iff.mp hK ⟨f, hFJ hf⟩
  simpa only [mem_centralizerJ_iff] using this

theorem commutator_eq_of_centralizerJ_eq_of_odd (h : Tim79a.ParrottHyp z)
    (L : Subgroup ↥(H z)) (hL : Odd (Nat.card L)) (hLZ : ∀ ℓ ∈ L, conjZ z ℓ = 1)
    {σ τ : ↥(H z)} (hσL : σ ∈ L) (hτL : τ ∈ L) (hσ : orderOf σ = 3) (hτ : orderOf τ = 3)
    (hVσ : conjV h σ ≠ 1) (hVτ : conjV h τ ≠ 1) (hK : centralizerJ σ = centralizerJ τ) :
    ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ =
      ⁅(Subgroup.zpowers τ).map (H z).subtype, J z⁆ := by
  obtain ⟨F', hF'J, hF'⟩ := exists_complement_commutator h L hL hLZ
  rw [(hF' σ hσL hσ hVσ).1, (hF' τ hτL hτ hVτ).1,
    inf_centralizer_eq_of_centralizerJ_eq hK hF'J]

theorem commutator_eq_of_centralizerJ_eq_of_commute (h : Tim79a.ParrottHyp z)
    {σ τ : ↥(H z)} (hσ : orderOf σ = 3) (hτ : orderOf τ = 3)
    (hZσ : conjZ z σ = 1) (hZτ : conjZ z τ = 1) (hVσ : conjV h σ ≠ 1) (hVτ : conjV h τ ≠ 1)
    (hcomm : σ * τ = τ * σ) (hK : centralizerJ σ = centralizerJ τ) :
    ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ =
      ⁅(Subgroup.zpowers τ).map (H z).subtype, J z⁆ := by
  have hc : Commute σ τ := hcomm
  have hab : ∀ a ∈ Subgroup.zpowers σ, ∀ b ∈ Subgroup.zpowers τ, Commute a b := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hc.zpow_zpow k l
  have hLZ : ∀ ℓ ∈ Subgroup.zpowers σ ⊔ Subgroup.zpowers τ, conjZ z ℓ = 1 := by
    intro ℓ hℓ
    have hle : Subgroup.zpowers σ ⊔ Subgroup.zpowers τ ≤ (conjZ z).ker :=
      sup_le (Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr hZσ))
        (Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr hZτ))
    exact MonoidHom.mem_ker.mp (hle hℓ)
  have hodd : Odd (Nat.card (Subgroup.zpowers σ ⊔ Subgroup.zpowers τ : Subgroup ↥(H z))) := by
    have hp : IsPGroup 3 ↥(Subgroup.zpowers σ ⊔ Subgroup.zpowers τ : Subgroup ↥(H z)) := by
      intro g
      refine ⟨1, ?_⟩
      obtain ⟨a, ha, b, hb, hab'⟩ := (CFSG.mem_sup_of_commute hab).mp g.2
      have ha3 : a ^ 3 = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hσ,
          pow_orderOf_eq_one, one_zpow]
      have hb3 : b ^ 3 = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hτ,
          pow_orderOf_eq_one, one_zpow]
      apply Subtype.ext
      rw [pow_one, Subgroup.coe_pow, ← hab', (hab a ha b hb).mul_pow, ha3, hb3, mul_one]
      rfl
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  exact commutator_eq_of_centralizerJ_eq_of_odd h _ hodd hLZ
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers σ))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)) hσ hτ hVσ hVτ hK

private theorem conj_mem_J (g : ↥(H z)) {j : G} (hj : j ∈ J z) :
    (g : G) * j * (g : G)⁻¹ ∈ J z := by
  have := (conjJ' z g ⟨j, hj⟩).2
  rwa [conjJ'_apply_coe] at this

private theorem conj_mem_commutator {Q : Subgroup G} {g : ↥(H z)}
    (hg : ∀ x ∈ Q, (g : G) * x * (g : G)⁻¹ ∈ Q) {p : G} (hp : p ∈ ⁅Q, J z⁆) :
    (g : G) * p * (g : G)⁻¹ ∈ ⁅Q, J z⁆ := by
  have key : ⁅Q, J z⁆ ≤ (⁅Q, J z⁆).comap (MulAut.conj (g : G)).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx j hj
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj (g : G)).toMonoidHom ⁅x, j⁆ =
        ⁅(g : G) * x * (g : G)⁻¹, (g : G) * j * (g : G)⁻¹⁆ := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
        commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (hg x hx) (conj_mem_J g hj)
  have := key hp
  simpa [MulAut.conj_apply] using this

theorem le_normalizer_commutator_of_generation (h : Tim79a.ParrottHyp z) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : orderOf σ₁ = 3) (hσ₂ : orderOf σ₂ = 3) (hZ₁ : conjZ z σ₁ = 1)
    (hZ₂ : conjZ z σ₂ = 1) (hV₁ : conjV h σ₁ ≠ 1) (hV₂ : conjV h σ₂ ≠ 1)
    (hcomm : σ₂ * σ₁ = σ₁ * σ₂) (hK : centralizerJ σ₁ = centralizerJ σ₂)
    (hgen : (J z).subgroupOf (H z) ⊔
        Subgroup.normalizer ((Subgroup.zpowers σ₁ : Subgroup ↥(H z)) : Set ↥(H z)) ⊔
        Subgroup.centralizer ({σ₂} : Set ↥(H z)) = ⊤) :
    H z ≤ Subgroup.normalizer
      ((⁅(Subgroup.zpowers σ₁).map (H z).subtype, J z⁆ : Subgroup G) : Set G) := by
  have hLZ : ∀ ℓ ∈ Subgroup.zpowers σ₁, conjZ z ℓ = 1 := by
    intro ℓ hℓ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hℓ
    rw [map_zpow, hZ₁, one_zpow]
  have hodd : Odd (Nat.card (Subgroup.zpowers σ₁)) := by
    rw [Nat.card_zpowers, hσ₁]
    decide
  obtain ⟨F', hF'J, hF'⟩ := exists_complement_commutator h (Subgroup.zpowers σ₁) hodd hLZ
  obtain ⟨hKeq, hzK⟩ := hF' σ₁ (Subgroup.mem_zpowers σ₁) hσ₁ hV₁
  have hKcomm := commutator_eq_of_centralizerJ_eq_of_commute h hσ₁ hσ₂ hZ₁ hZ₂ hV₁ hV₂
    hcomm.symm hK
  have hKJ : ⁅(Subgroup.zpowers σ₁).map (H z).subtype, J z⁆ ≤ J z :=
    (hKeq ▸ inf_le_left).trans hF'J
  have hJJ : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm', -, -⟩ := h
    simpa [J, H] using hcomm'
  have hzK' : Subgroup.zpowers z ≤ ⁅(Subgroup.zpowers σ₁).map (H z).subtype, J z⁆ :=
    Subgroup.zpowers_le.mpr hzK
  have hJ : (J z).subgroupOf (H z) ≤ (Subgroup.normalizer
      ((⁅(Subgroup.zpowers σ₁).map (H z).subtype, J z⁆ : Subgroup G) : Set G)).comap
        (H z).subtype := by
    intro g hg
    have hgJ : (g : G) ∈ J z := Subgroup.mem_subgroupOf.mp hg
    refine mem_normalizer_of_forall_mem (M := J z) (fun m hm v hv => ?_) hgJ
    have hc : ⁅m, v⁆ ∈ Subgroup.zpowers z :=
      hJJ ▸ Subgroup.commutator_mem_commutator hm (hKJ hv)
    have e : m * v * m⁻¹ = ⁅m, v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hzK' hc) hv
  have hN : Subgroup.normalizer ((Subgroup.zpowers σ₁ : Subgroup ↥(H z)) : Set ↥(H z)) ≤
      (Subgroup.normalizer
        ((⁅(Subgroup.zpowers σ₁).map (H z).subtype, J z⁆ : Subgroup G) : Set G)).comap
          (H z).subtype := by
    intro n hn
    refine mem_normalizer_of_forall_mem
      (M := (Subgroup.normalizer ((Subgroup.zpowers σ₁ : Subgroup ↥(H z)) :
        Set ↥(H z))).map (H z).subtype) (fun m hm v hv => ?_) ⟨n, hn, rfl⟩
    obtain ⟨n', hn', rfl⟩ := hm
    refine conj_mem_commutator (g := n') (fun x hx => ?_) hv
    obtain ⟨m', hm', rfl⟩ := hx
    exact ⟨n' * m' * n'⁻¹, (Subgroup.mem_normalizer_iff.mp hn' m').mp hm', rfl⟩
  have hC : Subgroup.centralizer ({σ₂} : Set ↥(H z)) ≤ (Subgroup.normalizer
      ((⁅(Subgroup.zpowers σ₁).map (H z).subtype, J z⁆ : Subgroup G) : Set G)).comap
        (H z).subtype := by
    intro c hc
    rw [Subgroup.mem_comap, hKcomm]
    refine mem_normalizer_of_forall_mem
      (M := (Subgroup.centralizer ({σ₂} : Set ↥(H z))).map (H z).subtype)
        (fun m hm v hv => ?_) ⟨c, hc, rfl⟩
    obtain ⟨c', hc', rfl⟩ := hm
    refine conj_mem_commutator (g := c') (fun x hx => ?_) hv
    obtain ⟨m', hm', rfl⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm'
    have hcc : Commute c' σ₂ := Subgroup.mem_centralizer_singleton_iff.mp hc'
    refine ⟨σ₂ ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, ?_⟩
    have := congrArg (H z).subtype (hcc.zpow_right k).mul_inv_cancel
    simpa using this.symm
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥(H z)) ∈ (⊤ : Subgroup ↥(H z)) := Subgroup.mem_top _
  rw [← hgen] at hmem
  exact (sup_le (sup_le hJ hN) hC) hmem

theorem commutator_normal_of_generation (h : Tim79a.ParrottHyp z) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : orderOf σ₁ = 3) (hσ₂ : orderOf σ₂ = 3) (hZ₁ : conjZ z σ₁ = 1)
    (hZ₂ : conjZ z σ₂ = 1) (hV₁ : conjV h σ₁ ≠ 1) (hV₂ : conjV h σ₂ ≠ 1)
    (hcomm : σ₂ * σ₁ = σ₁ * σ₂) (hK : centralizerJ σ₁ = centralizerJ σ₂)
    (hgen : (J z).subgroupOf (H z) ⊔
        Subgroup.normalizer ((Subgroup.zpowers σ₁ : Subgroup ↥(H z)) : Set ↥(H z)) ⊔
        Subgroup.centralizer ({σ₂} : Set ↥(H z)) = ⊤)
    (g : ↥(H z)) (p : G) :
    p ∈ ⁅(Subgroup.zpowers σ₁).map (H z).subtype, J z⁆ →
      (g : G) * p * (g : G)⁻¹ ∈ ⁅(Subgroup.zpowers σ₁).map (H z).subtype, J z⁆ := fun hp =>
  (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_commutator_of_generation h hσ₁ hσ₂ hZ₁ hZ₂ hV₁ hV₂ hcomm hK hgen g.2) p).mp hp

end CFSG.RankThree.GF2n.Parrott
