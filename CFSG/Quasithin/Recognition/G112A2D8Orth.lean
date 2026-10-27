module

public import CFSG.Quasithin.Recognition.G112A2D8S7

public section

namespace CFSG.Quasithin.G112A2

open Module CFSG.Open

section PermCore

open Equiv

theorem one_add_single_mem (k : Fin 5) :
    (1 + Pi.single k 1 : Fin 5 → ZMod 2) ∈ permCore 5 := by
  show ∑ i, (1 + Pi.single k 1 : Fin 5 → ZMod 2) i = 0
  simp only [Pi.add_apply, Pi.one_apply, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Finset.sum_pi_single', Finset.mem_univ, if_true]
  decide

@[expose] def coreImg (σ : Perm (Fin 5)) (k : Fin 5) : Fin 5 → ZMod 2 :=
  permAct σ (1 + Pi.single k 1) - (1 + Pi.single k 1)

theorem coreImg_apply (σ : Perm (Fin 5)) (k m : Fin 5) :
    coreImg σ k m = (if m = σ k then 1 else 0) - (if m = k then 1 else 0) := by
  simp only [coreImg, permAct, Pi.sub_apply, Pi.add_apply, Pi.one_apply, Pi.single_apply,
    Perm.inv_eq_iff_eq]
  ring

theorem exists_pair_of_ne_one {σ : Perm (Fin 5)} (hσ : σ ∈ alternatingGroup (Fin 5))
    (h1 : σ ≠ 1) : ∃ i j : Fin 5, coreImg σ i ≠ 0 ∧ coreImg σ j ≠ 0 ∧ coreImg σ i ≠ coreImg σ j := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
    by_contra h
    push Not at h
    exact h1 (Equiv.ext h)
  have hk0 : ∀ k, σ k ≠ k → coreImg σ k ≠ 0 := fun k hk h => by
    have := congrFun h k
    rw [coreImg_apply] at this
    simp [Ne.symm hk] at this
  by_contra hno
  push Not at hno
  have hmov : ∀ k, σ k ≠ k → (k = p ∨ k = σ p) ∧ (σ k = p ∨ σ k = σ p) := by
    intro k hk
    have he := hno k p (hk0 k hk) (hk0 p hp)
    have h1 := congrFun he k
    have h2 := congrFun he (σ k)
    rw [coreImg_apply, coreImg_apply] at h1 h2
    constructor
    · by_contra hc
      push Not at hc
      simp [Ne.symm hk, hc.1, hc.2] at h1 <;> exact absurd h1 (by decide)
    · by_contra hc
      push Not at hc
      simp [hk, hc.1, hc.2] at h2 <;> exact absurd h2 (by decide)
  have hsq : σ (σ p) = p := by
    have hmq : σ (σ p) ≠ σ p := fun h => hp (σ.injective h)
    rcases (hmov _ hmq).2 with h | h
    · exact h
    · exact absurd h hmq
  have heq : σ = swap p (σ p) := by
    ext k
    by_cases hk : σ k = k
    · have hkp : k ≠ p := fun h => hp (h ▸ hk)
      have hkq : k ≠ σ p := fun h => by
        rw [h] at hk
        exact hp (σ.injective hk)
      rw [swap_apply_of_ne_of_ne hkp hkq, hk]
    · rcases (hmov k hk).1 with rfl | rfl
      · rw [swap_apply_left]
      · rw [swap_apply_right, hsq]
  have hs := Perm.mem_alternatingGroup.mp hσ
  rw [heq, Perm.sign_swap (Ne.symm hp)] at hs
  exact absurd hs (by decide)

theorem five_le_card_permCore : 5 ≤ Nat.card (permCore 5) := by
  have hf : Function.Injective (fun k : Fin 5 => (⟨_, one_add_single_mem k⟩ : permCore 5)) := by
    intro i j hij
    have h := congrFun (congrArg Subtype.val hij) i
    by_contra hne
    simp [Pi.single_apply, Ne.symm hne] at h
  have := Nat.card_le_card_of_injective _ hf
  simpa using this

end PermCore

section Linear

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem mem_commSpanOf {L : Subgroup (V ≃ₗ[ZMod 2] V)} {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ L) (v : V) :
    γ v - v ∈ commSpanOf L :=
  Submodule.subset_span ⟨γ, hγ, v, rfl⟩

theorem map_mem_commSpanOf_self {L : Subgroup (V ≃ₗ[ZMod 2] V)} {γ : V ≃ₗ[ZMod 2] V}
    (hγ : γ ∈ L) {v : V} (hv : v ∈ commSpanOf L) : γ v ∈ commSpanOf L := by
  have := (commSpanOf L).add_mem hv (mem_commSpanOf hγ v)
  rwa [add_sub_cancel] at this

theorem map_mem_commSpanOf_of_commute {L' : Subgroup (V ≃ₗ[ZMod 2] V)} {γ : V ≃ₗ[ZMod 2] V}
    (hγ : ∀ δ ∈ L', γ * δ = δ * γ) {v : V} (hv : v ∈ commSpanOf L') : γ v ∈ commSpanOf L' := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨δ, hδ, u, rfl⟩ := hw
    have hc := congrArg (fun g : V ≃ₗ[ZMod 2] V => g u) (hγ δ hδ)
    simp only [LinearEquiv.mul_apply] at hc
    rw [map_sub, hc]
    exact mem_commSpanOf hδ (γ u)
  | zero => simp
  | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

theorem map_mem_commSpanOf_conj {L : Subgroup (V ≃ₗ[ZMod 2] V)} (x : V ≃ₗ[ZMod 2] V) {v : V}
    (hv : v ∈ commSpanOf L) : x v ∈ commSpanOf (L.map (MulAut.conj x).toMonoidHom) := by
  have hinv : ∀ u, x⁻¹ (x u) = u := fun u => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨δ, hδ, u, rfl⟩ := hw
    refine Submodule.subset_span ⟨x * δ * x⁻¹, ⟨δ, hδ, rfl⟩, x u, ?_⟩
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv]
  | zero => simp
  | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

theorem fix_of_commute {L L' : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (hcompl : IsCompl (commSpanOf L) (commSpanOf L'))
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ L) {v : V} (hv : v ∈ commSpanOf L') : a v = v := by
  have h2 : a v - v ∈ commSpanOf L' :=
    sub_mem (map_mem_commSpanOf_of_commute (fun δ hδ => hc a ha δ hδ) hv) hv
  have : a v - v ∈ commSpanOf L ⊓ commSpanOf L' := ⟨mem_commSpanOf ha v, h2⟩
  rw [hcompl.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at this
  exact this

end Linear

section Group

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a)
    {g : G} (hg : g ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, g = a * b := by
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ H, ∃ b ∈ K, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', H.mul_mem ha ha', b * b', K.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hc a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, by
          rw [mul_inv_rev]; exact (hc _ (H.inv_mem ha) _ (K.inv_mem hb)).symm⟩ }
  have hle : H ⊔ K ≤ P :=
    sup_le (fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩) (fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩)
  exact hle hg

theorem mem_or_mul_mem {X F : Subgroup G} {x : G} (hxX : x ∈ X)
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hsq : ∀ a ∈ X, a * a = 1)
    (hX : X = Subgroup.zpowers x ⊔ (X ⊓ F)) {t : G} (ht : t ∈ X) : t ∈ F ∨ x * t ∈ F := by
  let P : Subgroup G :=
    { carrier := {g | g ∈ X ∧ (g ∈ F ∨ x * g ∈ F)}
      mul_mem' := by
        rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
        refine ⟨X.mul_mem hg hh, ?_⟩
        rcases hg' with hg' | hg' <;> rcases hh' with hh' | hh'
        · exact Or.inl (F.mul_mem hg' hh')
        · right
          rw [← mul_assoc, hcomm x hxX g hg, mul_assoc]
          exact F.mul_mem hg' hh'
        · right
          rw [← mul_assoc]
          exact F.mul_mem hg' hh'
        · left
          have : g * h = x * g * (x * h) := by
            calc g * h = (x * x) * g * h := by rw [hsq x hxX, one_mul]
              _ = x * (x * g) * h := by group
              _ = x * (g * x) * h := by rw [hcomm x hxX g hg]
              _ = x * g * (x * h) := by group
          rw [this]
          exact F.mul_mem hg' hh'
      one_mem' := ⟨X.one_mem, Or.inl F.one_mem⟩
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        rw [inv_eq_of_mul_eq_one_right (hsq g hg)]
        exact ⟨hg, hg'⟩ }
  have hle : Subgroup.zpowers x ⊔ (X ⊓ F) ≤ P := by
    refine sup_le ((Subgroup.zpowers_le).mpr ⟨hxX, Or.inr ?_⟩) fun g hg => ⟨hg.1, Or.inl hg.2⟩
    rw [hsq x hxX]
    exact F.one_mem
  rw [hX] at ht
  exact (hle ht).2

end Group

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem finrank_ne_two_of_concl12 {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hsq : ∀ a ∈ X, a * a = 1)
    (h12 : G112Concl12 Γ X) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ X) :
    finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≠ 2 := by
  classical
  intro hr
  obtain ⟨-, x, L, hxX, -, -, hLL, hcL, hcompl, ⟨φ, ψ, hψ⟩, -, hXeq⟩ := h12
  set L' := L.map (MulAut.conj x).toMonoidHom with hL'
  set R := LinearMap.range (t.toLinearMap - LinearMap.id) with hR
  have hx2 : x * x = 1 := hsq x hxX
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxinj : ∀ u w : V, x u = x w → u = w := fun u w h => x.injective h
  have hcL' : ∀ a ∈ L', ∀ b ∈ L, a * b = b * a := fun a ha b hb => (hcL b hb a ha).symm
  have hV12 : commSpanOf L ⊓ commSpanOf L' = ⊥ := hcompl.inf_eq_bot
  have hdisj : ∀ v, v ∈ commSpanOf L → v ∈ commSpanOf L' → v = 0 := fun v h1 h2 => by
    have : v ∈ commSpanOf L ⊓ commSpanOf L' := ⟨h1, h2⟩
    rwa [hV12, Submodule.mem_bot] at this
  have hmemR : ∀ v, t v - v ∈ R := fun v => LinearMap.mem_range.mpr ⟨v, rfl⟩
  rcases mem_or_mul_mem hxX hcomm hsq hXeq ht with htF | htF
  ·
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcL htF
    obtain ⟨a', ha', hba⟩ := hb
    have hb' : b = x * a' * x⁻¹ := by rw [← hba]; rfl
    have hc : x * a * x⁻¹ ∈ L' := ⟨a, ha, rfl⟩
    have hbL' : b ∈ L' := ⟨a', ha', hba⟩
    have htx := hcomm x hxX _ ht
    have h1 : a * b = x * a * x⁻¹ * a' := by
      have e1 : a * b = x * (a * b) * x⁻¹ := by
        rw [htx]
        group
      have e2 : x * b * x⁻¹ = a' := by
        rw [hb']
        calc x * (x * a' * x⁻¹) * x⁻¹ = (x * x) * a' * (x * x)⁻¹ := by group
          _ = a' := by rw [hx2]; group
      rw [e1, show x * (a * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹) by group, e2]
    have h2 : a'⁻¹ * a = x * a * x⁻¹ * b⁻¹ := by
      have e3 := hcL a' ha' _ hc
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * (x * a * x⁻¹)) * b⁻¹ := by rw [h1, e3]
        _ = x * a * x⁻¹ * b⁻¹ := by group
    have h3 : a'⁻¹ * a ∈ L ⊓ L' :=
      ⟨L.mul_mem (L.inv_mem ha') ha, h2 ▸ L'.mul_mem hc (L'.inv_mem hbL')⟩
    rw [hLL, Subgroup.mem_bot, h2, mul_inv_eq_one] at h3
    have hbx : b = x * a * x⁻¹ := h3.symm
    by_cases ha1 : a = 1
    · have hb1 : b = 1 := by rw [hbx, ha1]; group
      rw [hR, ha1, hb1, one_mul] at hr
      have h0 : ((1 : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) = 0 := by
        ext v; simp
      rw [h0, LinearMap.range_zero, finrank_bot] at hr
      exact absurd hr (by norm_num)
    set σ : Equiv.Perm (Fin 5) := (φ ⟨a, ha⟩).1 with hσ
    have hσ1 : σ ≠ 1 := fun h => by
      apply ha1
      have : φ ⟨a, ha⟩ = 1 := Subtype.ext h
      rw [map_eq_one_iff φ φ.injective] at this
      exact congrArg Subtype.val this
    obtain ⟨i, j, hi0, hj0, hij⟩ := exists_pair_of_ne_one (φ ⟨a, ha⟩).2 hσ1
    let y : Fin 5 → commSpanOf L := fun k => ψ.symm ⟨_, one_add_single_mem k⟩
    have hψz : ∀ k, (ψ ⟨a (y k) - y k, sub_mem (map_mem_commSpanOf_self ha (y k).2) (y k).2⟩ :
        Fin 5 → ZMod 2) = coreImg σ k := by
      intro k
      have hw := hψ ⟨a, ha⟩ (y k) ⟨a (y k), map_mem_commSpanOf_self ha (y k).2⟩ rfl
      have he : (⟨a (y k) - y k, sub_mem (map_mem_commSpanOf_self ha (y k).2) (y k).2⟩ :
          commSpanOf L) = ⟨a (y k), map_mem_commSpanOf_self ha (y k).2⟩ - y k := rfl
      let Ψ : commSpanOf L →ₗ[ZMod 2] (Fin 5 → ZMod 2) := (permCore 5).subtype ∘ₗ ψ.toLinearMap
      have hΨ : ∀ u, Ψ u = (ψ u : Fin 5 → ZMod 2) := fun _ => rfl
      rw [← hΨ, he, map_sub, hΨ, hΨ, hw]
      simp only [y, LinearEquiv.apply_symm_apply]
      rfl
    set zi : V := a (y i) - y i with hzi
    set zj : V := a (y j) - y j with hzj
    have hziV : zi ∈ commSpanOf L := sub_mem (map_mem_commSpanOf_self ha (y i).2) (y i).2
    have hzjV : zj ∈ commSpanOf L := sub_mem (map_mem_commSpanOf_self ha (y j).2) (y j).2
    have hzi0 : zi ≠ 0 := fun h => by
      apply hi0
      rw [← hψz i]
      have : (⟨zi, hziV⟩ : commSpanOf L) = 0 := Subtype.ext h
      simp only [← hzi, this, map_zero, Submodule.coe_zero]
    have hzj0 : zj ≠ 0 := fun h => by
      apply hj0
      rw [← hψz j]
      have : (⟨zj, hzjV⟩ : commSpanOf L) = 0 := Subtype.ext h
      simp only [← hzj, this, map_zero, Submodule.coe_zero]
    have hzij : zi ≠ zj := fun h => by
      apply hij
      rw [← hψz i, ← hψz j]
      have : (⟨zi, hziV⟩ : commSpanOf L) = ⟨zj, hzjV⟩ := Subtype.ext h
      simp only [← hzi, ← hzj, this]
    have hbfix : ∀ v ∈ commSpanOf L, b v = v := fun v hv =>
      fix_of_commute hcL' hcompl.symm hbL' hv
    have hafix : ∀ v ∈ commSpanOf L', a v = v := fun v hv => fix_of_commute hcL hcompl ha hv
    have hzR : ∀ k, a (y k) - y k ∈ R := fun k => by
      have := hmemR (y k)
      rwa [LinearEquiv.mul_apply, hbfix _ (y k).2] at this
    have hxzR : x zi ∈ R := by
      have := hmemR (x (y i))
      have e : b (x (y i)) = x (a (y i)) := by
        rw [hbx, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxinv]
        congr 2
        rw [← LinearEquiv.mul_apply, hx2]
        rfl
      rw [LinearEquiv.mul_apply, e, hafix _ (map_mem_commSpanOf_conj x
        (map_mem_commSpanOf_self ha (y i).2)), ← map_sub] at this
      exact this
    have hxzV : x zi ∈ commSpanOf L' := map_mem_commSpanOf_conj x hziV
    have hxz0 : x zi ≠ 0 := fun h => hzi0 (hxinj _ _ (h.trans (map_zero x).symm))
    have hle : finrank (ZMod 2) ↥(R ⊓ commSpanOf L) ≤ 2 :=
      (Submodule.finrank_mono inf_le_left).trans hr.le
    have hziI : zi ∈ R ⊓ commSpanOf L := ⟨hzR i, hziV⟩
    have hzjI : zj ∈ R ⊓ commSpanOf L := ⟨hzR j, hzjV⟩
    obtain ⟨m, hm⟩ : ∃ m, finrank (ZMod 2) ↥(R ⊓ commSpanOf L) = m := ⟨_, rfl⟩
    rw [hm] at hle
    interval_cases m
    · rw [Submodule.finrank_eq_zero] at hm
      rw [hm, Submodule.mem_bot] at hziI
      exact hzi0 hziI
    · rcases eq_zero_or_eq_of_finrank_one hm hziI hzi0 hzjI with h | h
      · exact hzj0 h
      · exact hzij h.symm
    · have heq : R ⊓ commSpanOf L = R :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (hm.trans hr.symm)
      have hmem : x zi ∈ R ⊓ commSpanOf L := by
        rw [heq]
        exact hxzR
      have : x zi ∈ commSpanOf L := hmem.2
      exact hxz0 (hdisj _ this hxzV)
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup hcL htF
    have hbL' : b ∈ L' := hb
    have htv : ∀ v ∈ commSpanOf L, t v ∈ commSpanOf L' := fun v hv => by
      have et : t = x * (a * b) := by
        rw [← hab, ← mul_assoc, hx2, one_mul]
      rw [et, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        fix_of_commute hcL' hcompl.symm hbL' hv]
      exact map_mem_commSpanOf_conj x (map_mem_commSpanOf_self ha hv)
    let f : commSpanOf L →ₗ[ZMod 2] R :=
      ((t.toLinearMap - LinearMap.id).domRestrict (commSpanOf L)).codRestrict R
        (fun v => hmemR v)
    have hf : Function.Injective f := by
      intro u w huw
      have h := congrArg Subtype.val huw
      simp only [f, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, sub_apply_eq] at h
      have h' : t ((u : V) - w) = ((u : V) - w) := by
        rw [map_sub]
        exact sub_eq_sub_iff_sub_eq_sub.mp h
      have hm : ((u : V) - w) ∈ commSpanOf L := sub_mem u.2 w.2
      have h0 := hdisj _ hm (h' ▸ htv _ hm)
      exact Subtype.ext (sub_eq_zero.mp h0)
    have hle := LinearMap.finrank_le_finrank_of_injective hf
    rw [hr] at hle
    have hc := natCard_eq_two_pow (commSpanOf L)
    rw [Nat.card_congr ψ.toEquiv] at hc
    have h5 := five_le_card_permCore
    rw [hc] at h5
    have : 2 ^ finrank (ZMod 2) (commSpanOf L) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
    omega

theorem g112ConclA2_concl12 (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V) (W : Submodule (ZMod 2) V)
    (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (hH : G111Hyp B Γ v₁ W X X₀) (h12 : G112Concl12 Γ X) :
    ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
      v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  intro t ht hr _ _
  exact absurd hr (finrank_ne_two_of_concl12 hH.X_comm hH.X_sq h12 ht)

end Main

end CFSG.Quasithin.G112A2
