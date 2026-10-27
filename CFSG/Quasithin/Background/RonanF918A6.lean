module

public import CFSG.Quasithin.Background.Sp4InfDer
public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.Quasithin.Background.F918Fine4PfHat6

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section Abstract

@[expose] def conjSubHom {V : Type*} [CommGroup V] (L : Subgroup (MulAut V)) (t : MulAut V)
    (ht : ∀ l ∈ L, t * l * t⁻¹ ∈ L) : ↥L →* ↥L where
  toFun l := ⟨t * (l : MulAut V) * t⁻¹, ht l l.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem realizesVia_map_conj {V : Type*} [CommGroup V] {D : FFModel} {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥L} (h : D.RealizesVia L U Z π) (t : MulAut V)
    (ht : ∀ l ∈ L, t * l * t⁻¹ ∈ L) (ht' : ∀ l ∈ L, t⁻¹ * l * t ∈ L) :
    D.RealizesVia L (U.map t.toMonoidHom) (Z.map t.toMonoidHom) ((conjSubHom L t ht).comp π) := by
  obtain ⟨hπs, hZU, hkerle, hUinv, hZinv, hsec, hkinv, β, hβs, hβk, hβe⟩ := h
  have hinjt : Function.Injective t.toMonoidHom := t.injective
  let e : ↥U ≃* ↥(U.map t.toMonoidHom) := Subgroup.equivMapOfInjective U t.toMonoidHom hinjt
  have he : ∀ u : ↥U, ((e u : ↥(U.map t.toMonoidHom)) : V) = t (u : V) := fun u => rfl
  have hconj_surj : Function.Surjective (conjSubHom L t ht) := by
    intro l
    refine ⟨⟨t⁻¹ * (l : MulAut V) * t, ht' l l.2⟩, ?_⟩
    apply Subtype.ext
    show t * (t⁻¹ * (l : MulAut V) * t) * t⁻¹ = l
    group
  have hinv : ∀ (S : Subgroup V), (∀ h : ↥L, ∀ u ∈ S, (h : MulAut V) u ∈ S) →
      ∀ h : ↥L, ∀ u ∈ S.map t.toMonoidHom, (h : MulAut V) u ∈ S.map t.toMonoidHom := by
    intro S hS l u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨(t⁻¹ * (l : MulAut V) * t) v, hS ⟨t⁻¹ * (l : MulAut V) * t, ht' l l.2⟩ v hv, ?_⟩
    show t ((t⁻¹ * (l : MulAut V) * t) v) = (l : MulAut V) (t v)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  refine ⟨hconj_surj.comp hπs, Subgroup.map_mono hZU, hkerle, hinv U hUinv, hinv Z hZinv, hsec,
    hkinv, β.comp e.symm.toMonoidHom, hβs.comp e.symm.surjective, ?_, ?_⟩
  · intro w
    obtain ⟨u, rfl⟩ := e.surjective w
    show β (e.symm (e u)) = 1 ↔ _
    rw [MulEquiv.symm_apply_apply, hβk, he]
    exact (Subgroup.mem_map_iff_mem hinjt (K := Z) (x := (u : V))).symm
  · intro γ w m hw hm hwm
    obtain ⟨u, rfl⟩ := e.surjective w
    have hum : β u = QuotientGroup.mk m := by
      have : β (e.symm (e u)) = QuotientGroup.mk m := hwm
      rwa [MulEquiv.symm_apply_apply] at this
    have hu' : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := hUinv (π γ) u u.2
    have key := hβe γ u m hu' hm hum
    have hel : e.symm ⟨(((conjSubHom L t ht).comp π γ : ↥L) : MulAut V) ((e u : ↥(U.map t.toMonoidHom)) : V),
        hw⟩ = ⟨((π γ : ↥L) : MulAut V) (u : V), hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show (t * ((π γ : ↥L) : MulAut V) * t⁻¹) (t (u : V)) = t (((π γ : ↥L) : MulAut V) (u : V))
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    show β (e.symm ⟨_, hw⟩) = _
    rw [hel]
    exact key

theorem secIsoL_of_realizesVia_same {V : Type} [CommGroup V] {D : FFModel} {L : Subgroup (MulAut V)}
    {U₁ Z₁ U₂ Z₂ : Subgroup V} {π : D.Gam →* ↥L} (h₁ : D.RealizesVia L U₁ Z₁ π)
    (h₂ : D.RealizesVia L U₂ Z₂ π) : SecIsoL L U₁ Z₁ U₂ Z₂ := by
  obtain ⟨hπs, hZU₁, hkerle, hUinv₁, hZinv₁, hsec, hkinv, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := h₁
  obtain ⟨-, hZU₂, -, hUinv₂, hZinv₂, -, -, β₂, hβ₂s, hβ₂k, hβ₂e⟩ := h₂
  have hker2 : β₂.ker = Z₂.subgroupOf U₂ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβ₂k u
  let κ : ↥U₂ ⧸ Z₂.subgroupOf U₂ ≃* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (QuotientGroup.quotientMulEquivOfEq hker2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β₂ hβ₂s)
  have hκ : ∀ u : ↥U₂, κ (QuotientGroup.mk u) = β₂ u := fun u => rfl
  refine ⟨Function.surjective_id, hZU₁, hZU₂, fun g u hu => hUinv₁ g u hu,
    fun g z hz => hZinv₁ g z hz, fun g m hm => hUinv₂ g m hm, fun g m hm => hZinv₂ g m hm,
    κ.symm.toMonoidHom.comp β₁, κ.symm.surjective.comp hβ₁s, ?_, ?_⟩
  · intro u
    show κ.symm (β₁ u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, hβ₁k]
  · intro γ u m hu hm hum
    obtain ⟨δ, rfl⟩ := hπs γ
    let m' : ↥U₂ := m
    have hum' : β₁ u = β₂ m' := by
      have h1 : κ.symm (β₁ u) = QuotientGroup.mk m' := hum
      rw [← hκ m', ← h1, MulEquiv.apply_symm_apply]
    obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β₁ u)
    have hmact : D.act δ (m₀ : D.Amb) ∈ D.sec := hsec δ m₀ m₀.2
    have hu₁ : ((π δ : ↥L) : MulAut V) (u : V) ∈ U₁ := hUinv₁ (π δ) u u.2
    have hm₁ : ((π δ : ↥L) : MulAut V) (m' : V) ∈ U₂ := hUinv₂ (π δ) m' m'.2
    have e₁ := hβ₁e δ u m₀ hu₁ hmact hm₀.symm
    have e₂ := hβ₂e δ m' m₀ hm₁ hmact (by rw [← hum', ← hm₀])
    show κ.symm (β₁ ⟨((π δ : ↥L) : MulAut V) (u : V), hu₁⟩) =
      QuotientGroup.mk ⟨((π δ : ↥L) : MulAut V) (m' : V), hm₁⟩
    rw [MulEquiv.symm_apply_eq, hκ]
    exact e₁.trans e₂.symm

theorem secIsoL_of_inducedByS6 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥L} (h : (FFModel.altDn 6).RealizesVia L U Z π)
    (t : MulAut V) (ht : ∀ l ∈ L, t * l * t⁻¹ ∈ L) (ht' : ∀ l ∈ L, t⁻¹ * l * t ∈ L)
    (g : Equiv.Perm (Fin 6))
    (hg : ∀ y : ↥(alternatingGroup (Fin 6)), t * ((π y : ↥L) : MulAut V) * t⁻¹ =
      ((π (Sp4Inf.conjAlt6 g y) : ↥L) : MulAut V)) :
    SecIsoL L U Z (U.map t.toMonoidHom) (Z.map t.toMonoidHom) := by
  have h1 := realizesVia_map_conj h t ht ht'
  let θ : ↥(alternatingGroup (Fin 6)) →* ↥(alternatingGroup (Fin 6)) :=
    (Sp4Inf.conjAlt6 g⁻¹).toMonoidHom
  let Ê : ↥(FFModel.altDn 6).sec →* ↥(FFModel.altDn 6).sec := (G6.coreAct 6 g⁻¹).toMonoidHom
  have h2 := FFModel.RealizesVia.of_surjHom (FFModel.altDn_isActionModel 6) h1 θ
    (MulEquiv.surjective _) Ê (MulEquiv.surjective _)
    (fun σ m hm => by
      let σ' : ↥(alternatingGroup (Fin 6)) := σ
      let m' : ↥(G6.coreMod 6) := m
      show G6.permAct 6 g⁻¹ (G6.permAct 6 (σ' : Equiv.Perm (Fin 6)) (m' : G6.PermMod 6)) =
        G6.permAct 6 ((Sp4Inf.conjAlt6 g⁻¹ σ' : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
          (G6.permAct 6 g⁻¹ (m' : G6.PermMod 6))
      rw [← permAct_mul_act, ← permAct_mul_act, Sp4Inf.coe_conjAlt6]
      congr 1
      group)
    (fun m => by
      let m' : ↥(G6.coreMod 6) := m
      show (G6.permAct 6 g⁻¹ (m' : G6.PermMod 6)) ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 ↔
        (m' : G6.PermMod 6) ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6
      constructor
      · intro hm
        have := permAct_mem_ker 6 g hm
        rwa [← permAct_mul_act, mul_inv_cancel, permAct_one_act] at this
      · intro hm
        exact permAct_mem_ker 6 g⁻¹ hm)
  have h3 : ((conjSubHom L t ht).comp π).comp θ = π := by
    refine MonoidHom.ext fun y => Subtype.ext ?_
    show t * ((π (θ y) : ↥L) : MulAut V) * t⁻¹ = ((π y : ↥L) : MulAut V)
    rw [hg (θ y)]
    have hy : Sp4Inf.conjAlt6 g (θ y) = y := by
      show Sp4Inf.conjAlt6 g (Sp4Inf.conjAlt6 g⁻¹ y) = y
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hy]
  have h2' : (FFModel.altDn 6).RealizesVia L (U.map t.toMonoidHom) (Z.map t.toMonoidHom) π :=
    h3 ▸ h2
  exact secIsoL_of_realizesVia_same h h2'

end Abstract

section A6

open CFSG.QuasithinUnique.Lin2.Five (tauSp)

theorem exists_fusing_of_not_induced {α : MulAut ↥(alternatingGroup (Fin 6))}
    (hα : ¬ Sp4Inf.InducedByS6 α) :
    ∃ a : ↥(alternatingGroup (Fin 6)), a ^ 3 = 1 ∧ a ≠ 1 ∧
      ∀ β : ↥(alternatingGroup (Fin 6)), α a ≠ β * a * β⁻¹ := by
  obtain ⟨γ, hγ⟩ := (Sp4Inf.ext_alt6 α).resolve_left hα
  refine ⟨⟨Sp4Inf.iotaSp Sp4Inf.aSp, Sp4Inf.aSp_mem_alt⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (Sp4Inf.iotaSp Sp4Inf.aSp) ^ 3 = 1
    rw [← map_pow, Sp4Inf.aSp_pow_three, map_one]
  · intro h1
    have h2 : Sp4Inf.iotaSp Sp4Inf.aSp = 1 := congrArg Subtype.val h1
    have h3 : Sp4Inf.aSp = 1 := Sp4Inf.iotaSp.injective (by rw [h2, map_one])
    have h4 : (Sp4Inf.aM : Matrix Sp4Inf.I4 Sp4Inf.I4 (ZMod 2)) = 1 := by
      have := congrArg (fun g : StatedSp 2 (ZMod 2) =>
        ((g : GL Sp4Inf.I4 (ZMod 2)) : Matrix Sp4Inf.I4 Sp4Inf.I4 (ZMod 2))) h3
      simpa [Sp4Inf.coe_aSp] using this
    exact absurd h4 (by decide)
  · intro β hβ
    have h1 := congrArg Subtype.val hβ
    have h2 := hγ ⟨Sp4Inf.iotaSp Sp4Inf.aSp, Sp4Inf.aSp_mem_alt⟩
    rw [h2] at h1
    simp only [MulEquiv.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    set κ := Sp4Inf.iotaSp.symm (β : Equiv.Perm (Fin 6)) with hκ
    have h3 : Sp4Inf.iotaSp (γ * tauSp Sp4Inf.aSp * γ⁻¹) =
        Sp4Inf.iotaSp (κ * Sp4Inf.aSp * κ⁻¹) := by
      rw [h1, map_mul, map_mul, map_inv, hκ, MulEquiv.apply_symm_apply]
    have h4 : γ * tauSp Sp4Inf.aSp * γ⁻¹ = κ * Sp4Inf.aSp * κ⁻¹ := Sp4Inf.iotaSp.injective h3
    have key : tauSp Sp4Inf.aSp = (γ⁻¹ * κ) * Sp4Inf.aSp * (γ⁻¹ * κ)⁻¹ := by
      calc tauSp Sp4Inf.aSp = γ⁻¹ * (γ * tauSp Sp4Inf.aSp * γ⁻¹) * γ := by group
        _ = γ⁻¹ * (κ * Sp4Inf.aSp * κ⁻¹) * γ := by rw [h4]
        _ = (γ⁻¹ * κ) * Sp4Inf.aSp * (γ⁻¹ * κ)⁻¹ := by group
    have h6 := Sp4Inf.card_fix_conj Sp4Inf.aSp (γ⁻¹ * κ)
    rw [← key, Sp4Inf.card_fix_tau_aSp, Sp4Inf.card_fix_aSp] at h6
    omega

theorem alt_injective_of_surj {n : ℕ} (hn : 5 ≤ n) {Y : Type} [Group Y] {A : Subgroup Y}
    (hA : A ≠ ⊥) (π : ↥(alternatingGroup (Fin n)) →* ↥A) (hπ : Function.Surjective π) :
    Function.Injective π := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  have hne : ∃ s, π s ≠ 1 := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
    obtain ⟨s, rfl⟩ := hπ a
    exact ⟨s, ha1⟩
  exact injective_of_isSimpleGroup π hne

section Hat6

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem actH_conj_mem_autIH (h : HypF918 T V L V₁ Vp H K) (hK : conjClosure K T = K) {x : G}
    (hx : x ∈ H) {l : MulAut ↥(tildeOf V₁ (conjClosure I H))} (hl : l ∈ autIH V₁ I H K) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨x, hx⟩ * l *
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨x, hx⟩)⁻¹ ∈
        autIH V₁ I H K := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hl' : l ∈ (K.subgroupOf H).map
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [← autIH_eq_map h hKH]
    exact hl
  obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hl'
  have hxk : x * k * x⁻¹ ∈ K := by
    have hk' : k ∈ conjClosure K T := by rw [hK]; exact Subgroup.mem_subgroupOf.mp hk
    have := (Subgroup.mem_normalizer_iff.mp (h.K₀_normal hx) k).mp hk'
    rwa [hK] at this
  rw [autIH_eq_map h hKH]
  refine ⟨⟨x * k * x⁻¹, H.mul_mem (H.mul_mem hx hkH) (H.inv_mem hx)⟩,
    Subgroup.mem_subgroupOf.mpr hxk, ?_⟩
  show actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
      ((⟨x, hx⟩ : ↥H) * ⟨k, hkH⟩ * (⟨x, hx⟩ : ↥H)⁻¹) = _
  rw [map_mul, map_mul, map_inv]

theorem hat6_exclusion (hHat6 : F918Fine4Hat6) (hH : SQTKGroup ↥H) (h : HypF918 T V L V₁ Vp H K)
    (hK : conjClosure K T = K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    {t : MulAut ↥(tildeOf V₁ (conjClosure I H))} (ht : t ∈ autIH V₁ I H T)
    (halt6 : AlternatingNatural (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
      (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))) 6)
    (hsec : ¬ SecIsoL (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
      (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T)))
      ((subM V₁ (conjClosure I H) I).map t.toMonoidHom)
      ((subM V₁ (conjClosure I H) I).map t.toMonoidHom ⊓
        fixV (autIH V₁ I H (conjClosure K T)))) :
    ¬ IsHat ↥(autIH V₁ Vp H K) ↥(alternatingGroup (Fin 6)) := by
  intro hHat
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK]
  rw [hMp] at halt6 hsec
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hAne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  obtain ⟨π₂, hπ₂⟩ := halt6
  let π₀ : ↥(alternatingGroup (Fin 6)) →* ↥(autIH V₁ I H K) := π₂
  have hπ₀ : (FFModel.altDn 6).RealizesVia (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)
      (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H K)) π₀ := hπ₂
  have hinj : Function.Injective π₀ := alt_injective_of_surj (by norm_num) hAne π₀ hπ₀.1
  let π : ↥(alternatingGroup (Fin 6)) ≃* ↥(autIH V₁ I H K) :=
    MulEquiv.ofBijective π₀ ⟨hinj, hπ₀.1⟩
  have hπc : ∀ y, π y = π₀ y := fun y => rfl
  have ht' : t ∈ (T.subgroupOf H).map
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [← autIH_eq_map h h.T_le_H]
    exact ht
  obtain ⟨⟨s, hsH⟩, hsT, hts⟩ := ht'
  have hsT' : s ∈ T := Subgroup.mem_subgroupOf.mp hsT
  have htn : ∀ l ∈ autIH V₁ I H K, t * l * t⁻¹ ∈ autIH V₁ I H K := by
    intro l hl
    rw [← hts]
    exact actH_conj_mem_autIH h hK hsH hl
  have htn' : ∀ l ∈ autIH V₁ I H K, t⁻¹ * l * t ∈ autIH V₁ I H K := by
    intro l hl
    have h1 := actH_conj_mem_autIH h hK (H.inv_mem hsH) hl
    have e : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s⁻¹, H.inv_mem hsH⟩ = t⁻¹ := by
      rw [← hts, ← map_inv]
      rfl
    rw [e] at h1
    simpa using h1
  have hinjt : Function.Injective t.toMonoidHom := t.injective
  let cA : ↥(autIH V₁ I H K) ≃* ↥(autIH V₁ I H K) :=
    { toFun := fun l => ⟨t * (l : MulAut _) * t⁻¹, htn l l.2⟩
      invFun := fun l => ⟨t⁻¹ * (l : MulAut _) * t, htn' l l.2⟩
      left_inv := fun l => by
        apply Subtype.ext
        show t⁻¹ * (t * (l : MulAut _) * t⁻¹) * t = (l : MulAut _)
        group
      right_inv := fun l => by
        apply Subtype.ext
        show t * (t⁻¹ * (l : MulAut _) * t) * t⁻¹ = (l : MulAut _)
        group
      map_mul' := fun a b => by
        apply Subtype.ext
        show t * ((a : MulAut _) * (b : MulAut _)) * t⁻¹ =
          (t * (a : MulAut _) * t⁻¹) * (t * (b : MulAut _) * t⁻¹)
        group }
  let α : MulAut ↥(alternatingGroup (Fin 6)) := π.trans (cA.trans π.symm)
  have hαπ : ∀ y, π (α y) = cA (π y) := fun y => π.apply_symm_apply _
  by_cases hα : Sp4Inf.InducedByS6 α
  ·
    obtain ⟨g, hg⟩ := hα
    have hg' : ∀ y : ↥(alternatingGroup (Fin 6)),
        t * ((π₀ y : ↥(autIH V₁ I H K)) : MulAut _) * t⁻¹ =
        ((π₀ (Sp4Inf.conjAlt6 g y) : ↥(autIH V₁ I H K)) : MulAut _) := by
      intro y
      have h1 : α y = Sp4Inf.conjAlt6 g y := Subtype.ext (by rw [hg y, Sp4Inf.coe_conjAlt6])
      have h2 := hαπ y
      rw [h1] at h2
      exact (congrArg Subtype.val h2).symm
    have hS := secIsoL_of_inducedByS6 hπ₀ t htn htn' g hg'
    have hfixt : (fixV (autIH V₁ I H K)).map t.toMonoidHom = fixV (autIH V₁ I H K) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ a ha
        have h1 := hy (t⁻¹ * a * t) (htn' a ha)
        show a (t y) = t y
        have h2 : a (t y) = t ((t⁻¹ * a * t) y) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
        rw [h2, h1]
      · intro hx
        refine ⟨t⁻¹ x, fun a ha => ?_, ?_⟩
        · have h1 := hx (t * a * t⁻¹) (htn a ha)
          have h2 : a (t⁻¹ x) = t⁻¹ ((t * a * t⁻¹) x) := by
            rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
          rw [h2, h1]
        · show t (t⁻¹ x) = x
          rw [MulAut.apply_inv_self]
    have hZmap : (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H K)).map t.toMonoidHom =
        (subM V₁ (conjClosure I H) I).map t.toMonoidHom ⊓ fixV (autIH V₁ I H K) := by
      rw [Subgroup.map_inf _ _ _ hinjt, hfixt]
    rw [hZmap] at hS
    exact hsec hS
  ·
    obtain ⟨a₀, ha₃, ha1, hfus⟩ := exists_fusing_of_not_induced hα
    have hcen : Subgroup.center ↥(autIH V₁ I H K) = ⊥ := by
      have hZ6 : Subgroup.center ↥(alternatingGroup (Fin 6)) = ⊥ :=
        alternatingGroup.center_eq_bot (by simp)
      rw [← Subgroup.map_center_eq π, hZ6, Subgroup.map_bot]
    have hρs := toAutI_surjective h I
    have hclaim : ∀ y : ↥K, (y : G) ∈ oTwoZIn K ↔ toAutI h I y = 1 := by
      intro y
      rw [F918Fine4Pf.mem_oTwoZIn_iff_pCore]
      constructor
      · intro hc
        have hcentral : toAutI h I y ∈ Subgroup.center ↥(autIH V₁ I H K) := by
          rw [Subgroup.mem_center_iff]
          intro b
          obtain ⟨w, rfl⟩ := hρs b
          have h1 := hc w
          rw [← F918Fine4Pf.ker_toAutI_eq_pCore h] at h1
          have h2 : toAutI h I (y * w * y⁻¹ * w⁻¹) = 1 :=
            MonoidHom.mem_ker.mp (toAutI_ker_le h hIU h1)
          simp only [map_mul, map_inv] at h2
          have h3 := mul_inv_eq_one.mp h2
          exact (mul_inv_eq_iff_eq_mul.mp h3).symm
        rw [hcen, Subgroup.mem_bot] at hcentral
        exact hcentral
      · intro hy w
        rw [← F918Fine4Pf.ker_toAutI_eq_pCore h]
        exact toAutI_comm h hIU hnt y (MonoidHom.mem_ker.mpr hy) w
    obtain ⟨x, hx⟩ := hρs (π a₀)
    have hxs : ∀ z : ↥K, s * (z : G) * s⁻¹ ∈ K := by
      intro z
      have hz : (z : G) ∈ conjClosure K T := by rw [hK]; exact z.2
      have := (Subgroup.mem_normalizer_iff.mp (h.K₀_normal hsH) (z : G)).mp hz
      rwa [hK] at this
    have hF : FusesThreesModZ K s := by
      refine ⟨(x : G), x.2, ?_, ?_, ?_⟩
      · have h3 : toAutI h I (x ^ 3) = 1 := by
          rw [map_pow, hx, ← map_pow, ha₃, map_one]
        have := (hclaim (x ^ 3)).mpr h3
        simpa using this
      · intro hmem
        have h1 := (hclaim x).mp hmem
        rw [hx] at h1
        exact ha1 (π.injective (by rw [h1, map_one]))
      · intro k hk hmem
        let kk : ↥K := ⟨k, hk⟩
        let xs : ↥K := ⟨s * (x : G) * s⁻¹, hxs x⟩
        have hmem' : (((kk * x * kk⁻¹)⁻¹ * xs : ↥K) : G) ∈ oTwoZIn K := by
          simpa [kk, xs] using hmem
        have h1 := (hclaim _).mp hmem'
        simp only [map_mul, map_inv] at h1
        have h2 : toAutI h I xs = toAutI h I kk * toAutI h I x * (toAutI h I kk)⁻¹ := by
          have := inv_mul_eq_one.mp h1
          exact this.symm
        have h3 : toAutI h I xs = cA (toAutI h I x) := by
          apply Subtype.ext
          show actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
              (Subgroup.inclusion hKH xs) =
            t * actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
              (Subgroup.inclusion hKH x) * t⁻¹
          rw [← hts]
          have e : (Subgroup.inclusion hKH xs : ↥H) =
              ⟨s, hsH⟩ * Subgroup.inclusion hKH x * ⟨s, hsH⟩⁻¹ := rfl
          rw [e, map_mul, map_mul, map_inv]
        apply hfus (π.symm (toAutI h I kk))
        apply π.injective
        rw [hαπ, map_mul, map_mul, map_inv, π.apply_symm_apply, ← hx, ← h3, h2, hx]
    exact hHat6 G T V L V₁ Vp H K h hH hK hHat s hsT' hF

end Hat6

end A6

end CFSG.Quasithin.RonanF918
