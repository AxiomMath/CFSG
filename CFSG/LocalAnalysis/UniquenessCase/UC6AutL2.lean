module

public import CFSG.LocalAnalysis.UniquenessCase.UC6AutEbar
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qe

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Signalizer.L46E CFSG.GorensteinWalter
  CFSG.PSL2Table CFSG.GH74.GLS.IVK.L2Borel
open CFSG.LocalAnalysis.UniquenessCase.UC22 (uc22p22qe_card_unipotent uc22p22qe_unipotent_pow)
open CFSG.Blueprint (LieModel)

theorem absKC_psl2 {F : Type} [Field F] [Finite F] {r n : ℕ} [Fact r.Prime] (hF : Nat.card F = r ^ n)
    (W : Sylow r (PSL2 F)) : AbsKC (PSL2 F) r (W : Subgroup (PSL2 F)) :=
  fun α _ hα => l46e_aut_fix_sylow hF W α hα

theorem orderOf_conj_eq_pow {S : Type} [Group S] {r : ℕ} (hr : r.Prime) {E : Subgroup S}
    (hE : IsPGroup r E) {e : S} (he : e ∈ E) : ∃ k, orderOf (MulAut.conj e) = r ^ k := by
  obtain ⟨k, hk⟩ := hE ⟨e, he⟩
  have hk' : e ^ r ^ k = 1 := congrArg Subtype.val hk
  have h1 : (MulAut.conj e) ^ r ^ k = 1 := by rw [← map_pow, hk', map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).1 (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨j, hj⟩

theorem absKInv_psl2 {F : Type} [Field F] [Finite F] {r n : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hF : Nat.card F = r ^ n) (W : Sylow r (PSL2 F)) : AbsKInv (PSL2 F) (W : Subgroup (PSL2 F)) := by
  have key : ∀ x : MulAut (PSL2 F), (∃ k, orderOf x = 2 ^ k) → (∀ e ∈ (W : Subgroup (PSL2 F)), x e = e) →
      x = 1 := by
    rintro x ⟨k, hk⟩ hx
    obtain ⟨w, hw, rfl⟩ := l46e_aut_fix_sylow hF W x hx
    obtain ⟨j, hj⟩ := orderOf_conj_eq_pow (Fact.out : r.Prime) W.isPGroup' hw
    have hcop : Nat.Coprime (2 ^ k) (r ^ j) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two (Fact.out : r.Prime)).2 (Ne.symm hr2))
    rw [hk] at hj
    have : 2 ^ k = 1 := by
      have := hcop.eq_one_of_dvd (by rw [hj]) 
      exact this
    rw [← orderOf_eq_one_iff, hk, this]
  intro x y hx hy hxE hyE hx1 _
  exact absurd (key x hx hxE) hx1


theorem mulAut_mul_conj_mul_inv {S : Type} [Group S] (α : MulAut S) (g : S) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem conj_injective_of_center_eq_bot {S : Type} [Group S] (h : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hc : g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := congrArg (fun γ : MulAut S => γ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = (g * x * g⁻¹) * g := by rw [h1]
      _ = g * x := by group
  rw [h] at hc
  exact hc

theorem centralizer_eq_of_mem_sylow {F : Type} [Field F] [Finite F] {r n : ℕ} [Fact r.Prime]
    (hF : Nat.card F = r ^ n) (h2 : (2 : F) ≠ 0) (W : Sylow r (PSL2 F)) {e : PSL2 F}
    (he : e ∈ (W : Subgroup (PSL2 F))) (he1 : e ≠ 1) :
    Subgroup.centralizer {e} = (W : Subgroup (PSL2 F)) := by
  obtain ⟨c, hc⟩ := exists_conj_eq_unipotent hF W
  rw [hc] at he ⊢
  obtain ⟨u, hu, rfl⟩ := he
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists u).1 hu
  have ht : t ≠ 0 := by
    rintro rfl
    apply he1
    simp [unip_zero]
  have hcent := centralizer_mk_unip h2 ht
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map_equiv]
  have hg : ((MulAut.conj c).symm g) ∈ unipotent F ↔
      (MulAut.conj c).symm g ∈ Subgroup.centralizer {mk (unip t)} := by rw [hcent]
  rw [hg, Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc c⁻¹ * g * c * mk (unip t) = c⁻¹ * (g * (c * mk (unip t) * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * mk (unip t) * c⁻¹) * g) * c := by rw [h]
      _ = mk (unip t) * (c⁻¹ * g * c) := by group
  · intro h
    calc g * (c * mk (unip t) * c⁻¹) = c * ((c⁻¹ * g * c) * mk (unip t)) * c⁻¹ := by group
      _ = c * (mk (unip t) * (c⁻¹ * g * c)) * c⁻¹ := by rw [h]
      _ = (c * mk (unip t) * c⁻¹) * g := by group


theorem isElemAbelian_card_sylow_psl2 {F : Type} [Field F] [Finite F] {r n : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hF : Nat.card F = r ^ n) (hn : n ≠ 0) (W : Sylow r (PSL2 F)) :
    IsElemAbelian r (W : Subgroup (PSL2 F)) ∧ Nat.card (W : Subgroup (PSL2 F)) = r ^ n := by
  have hrp : r.Prime := Fact.out
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hrp.odd_of_ne_two hr2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.GLS.IVK.L2Borel.two_ne_zero_of_odd_card hodd
  have hchar : (r : F) = 0 := by
    haveI := Fintype.ofFinite F
    have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hF] at h0
    push_cast at h0
    exact pow_eq_zero_iff hn |>.1 h0
  obtain ⟨c, hc⟩ := exists_conj_eq_unipotent hF W
  have hcomm : ∀ a ∈ (W : Subgroup (PSL2 F)), ∀ b ∈ (W : Subgroup (PSL2 F)), a * b = b * a := by
    intro a ha b hb
    rw [hc] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := unipotent_mul_comm ha' hb'
    calc c * a' * c⁻¹ * (c * b' * c⁻¹) = c * (a' * b') * c⁻¹ := by group
      _ = c * (b' * a') * c⁻¹ := by rw [this]
      _ = c * b' * c⁻¹ * (c * a' * c⁻¹) := by group
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, fun a ha => ?_⟩, ?_⟩
  · rw [hc] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    rw [← map_pow, uc22p22qe_unipotent_pow hchar ha', map_one]
  · rw [hc, Subgroup.card_map_of_injective (MulAut.conj c).injective, uc22p22qe_card_unipotent h2, hF]

theorem absKN_generic {S : Type} [Group S] [Finite S] {r : ℕ} (hrp : r.Prime) {E : Subgroup S}
    (hEel : IsElemAbelian r E) (hE2 : r ^ 2 ≤ Nat.card E) (hcen : Subgroup.center S = ⊥)
    (hN : ∀ e ∈ E, e ≠ 1 → ∀ α : MulAut S, α e = e → ∀ e' ∈ E, α e' ∈ E)
    (hC : ∀ α : MulAut S, (∀ e ∈ E, α e = e) → ∃ k : ℕ, orderOf α = r ^ k) (isL34 : Prop) :
    AbsKN S r E isL34 := by
  classical
  intro X hEX hXr
  have hinj := conj_injective_of_center_eq_bot hcen
  have hEp : IsPGroup r E := IsElemAbelian.isPGroup hEel
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set A : Subgroup (MulAut S) := E.map (MulAut.conj : S →* MulAut S) with hA
  have hAel : IsElemAbelian r A := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      change (a : MulAut S) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, hEcomm a' ha' b' hb']
    · rintro _ ⟨a', ha', rfl⟩
      rw [← map_pow, hEel.2 a' ha', map_one]
  have hAcard : r ^ 2 ≤ Nat.card A := by
    rw [hA, Subgroup.card_map_of_injective hinj]
    exact hE2
  have hXcop : Nat.Coprime r (Nat.card X) := by
    by_contra hnc
    have hdvd : r ∣ Nat.card X := by
      by_contra h
      exact hnc ((Nat.Prime.coprime_iff_not_dvd hrp).2 h)
    haveI : Fact r.Prime := ⟨hrp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hx1 := hXr (x : MulAut S) x.2 ⟨1, by rw [Subgroup.orderOf_coe, hx, pow_one]⟩
    have h1 : orderOf (x : MulAut S) = 1 := by rw [hx1, orderOf_one]
    rw [Subgroup.orderOf_coe, hx] at h1
    exact hrp.one_lt.ne' h1
  have hAX : A ≤ Subgroup.normalizer (X : Set (MulAut S)) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hEX e he x hx
    · intro hx
      have h1 := hEX e⁻¹ (E.inv_mem he) _ hx
      rw [map_inv] at h1
      have h3 : (MulAut.conj e)⁻¹ * ((MulAut.conj e : MulAut S) * x * (MulAut.conj e)⁻¹) *
          ((MulAut.conj e)⁻¹)⁻¹ = x := by group
      rw [h3] at h1
      exact h1
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity hrp hAel hAcard
    hAX hXcop
  have hbot : X = ⊥ := by
    rw [eq_bot_iff, ← hgen]
    refine iSup_le fun a => iSup_le fun haA => iSup_le fun ha1 => ?_
    obtain ⟨e, he, rfl⟩ := haA
    have he1 : e ≠ 1 := fun h => ha1 (by rw [h, map_one])
    rintro t ⟨htX, htC⟩
    have htc : t * MulAut.conj e = MulAut.conj e * t := Subgroup.mem_centralizer_singleton_iff.1 htC
    have hte : t e = e := by
      apply hinj
      rw [← mulAut_mul_conj_mul_inv, htc]
      group
    have htW : ∀ e' ∈ E, t e' ∈ E := hN e he he1 t hte
    have htfix : ∀ e' ∈ E, t e' = e' := by
      intro e' he'
      have hcW : t e' * e'⁻¹ ∈ E := E.mul_mem (htW e' he') (E.inv_mem he')
      have hmem : MulAut.conj (t e' * e'⁻¹) ∈ X := by
        have h1 : MulAut.conj (t e' * e'⁻¹) = t * (MulAut.conj e' * t⁻¹ * (MulAut.conj e')⁻¹) := by
          rw [map_mul, map_inv, ← mulAut_mul_conj_mul_inv]
          group
        rw [h1]
        exact X.mul_mem htX (hEX e' he' t⁻¹ (X.inv_mem htX))
      obtain ⟨k, hk⟩ := orderOf_conj_eq_pow hrp hEp hcW
      have h1 : MulAut.conj (t e' * e'⁻¹) = 1 := hXr _ hmem ⟨k, hk⟩
      have h2' : t e' * e'⁻¹ = 1 := hinj (by rw [h1, map_one])
      exact mul_inv_eq_one.1 h2'
    have ht1 : t = 1 := hXr t htX (hC t htfix)
    rw [ht1]
    exact Subgroup.one_mem _
  refine ⟨fun x hx e _ => ?_, Or.inl hbot⟩
  rw [hbot, Subgroup.mem_bot] at hx
  rw [hx]
  rfl

theorem absKN_psl2 {F : Type} [Field F] [Finite F] {r n : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hF : Nat.card F = r ^ n) (hn : 2 ≤ n) (W : Sylow r (PSL2 F)) (isL34 : Prop) :
    AbsKN (PSL2 F) r (W : Subgroup (PSL2 F)) isL34 := by
  have hrp : r.Prime := Fact.out
  obtain ⟨hel, hcard⟩ := isElemAbelian_card_sylow_psl2 hr2 hF (by omega) W
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hrp.odd_of_ne_two hr2).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.GLS.IVK.L2Borel.two_ne_zero_of_odd_card hodd
  refine absKN_generic hrp hel (by rw [hcard]; exact Nat.pow_le_pow_right hrp.pos hn)
    (psl2_center_eq_bot F) ?_ ?_ isL34
  · intro e he he1 α hα e' he'
    have hCC := centralizer_eq_of_mem_sylow hF h2 W he he1
    have h1 : e' ∈ Subgroup.centralizer ({e} : Set (PSL2 F)) := by
      rw [hCC]
      exact he'
    have h3 : e' * e = e * e' := Subgroup.mem_centralizer_singleton_iff.1 h1
    have h4 : α e' ∈ Subgroup.centralizer ({e} : Set (PSL2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h5 := congrArg α h3
      rw [map_mul, map_mul, hα] at h5
      exact h5
    rw [hCC] at h4
    exact h4
  · intro α hα
    obtain ⟨w, hw, rfl⟩ := l46e_aut_fix_sylow hF W α hα
    exact orderOf_conj_eq_pow hrp W.isPGroup' hw

theorem absK_of_lieModel_sylow {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hL : LieModel S .PSL 2 r 2) (E : Subgroup S) (hE : IsSylowOf r E ⊤) (isL : Prop) :
    AbsKC S r E ∧ AbsKN S r E isL ∧ AbsKInv S E := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, _, _, e, -, hFq⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' hr hr2 hL
  let φ : S ≃* PSL2 F := CFSG.GH74.GLS.IVK.toPSL e
  obtain ⟨-, hSp, hSnd⟩ := isSylowOf_iff.1 hE
  let W : Sylow r S := hSp.toSylow (by simpa [Subgroup.relIndex_top_right] using hSnd)
  let W' : Sylow r (PSL2 F) := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective W
  have hW' : (W' : Subgroup (PSL2 F)) = E.map φ.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hE' : (W' : Subgroup (PSL2 F)).map φ.symm.toMonoidHom = E := by
    rw [hW', Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id S := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  refine ⟨?_, ?_, ?_⟩
  · have := AbsKC.of_mulEquiv φ.symm (absKC_psl2 hFq W')
    rwa [hE'] at this
  · have := AbsKN.of_mulEquiv φ.symm (absKN_psl2 hr2 hFq le_rfl W' isL)
    rwa [hE'] at this
  · have := AbsKInv.of_mulEquiv φ.symm (absKInv_psl2 hr2 hFq W')
    rwa [hE'] at this

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem isSylowOf_Ebar_of_lieModel (h620 : m.C620) (hL : LieModel m.Lbar .PSL 2 m.r 2) :
    IsSylowOf m.r m.Ebar ⊤ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hp : IsPGroup m.r m.Ebar := IsPGroup.of_card (m.card_Ebar h620)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hPsyl : IsSylowOf m.r (P : Subgroup m.Lbar) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hPcard := (UC22.uc22p22q_psl2_sylow_elem m.hr m.d.odd hL hPsyl).2
  have : m.Ebar = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, m.card_Ebar h620])
  rw [this]
  exact hPsyl

theorem kernels633_of_lieModel (h620 : m.C620) (hL : LieModel m.Lbar .PSL 2 m.r 2) :
    m.KC633 ∧ m.KN633 ∧ m.KInv633 := by
  obtain ⟨h1, h2, h3⟩ := absK_of_lieModel_sylow m.hr m.d.odd hL m.Ebar
    (m.isSylowOf_Ebar_of_lieModel h620 hL) (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2)
  exact ⟨m.kc633_of_abs h1, m.kn633_of_abs h2, m.kinv633_of_abs h3⟩

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
