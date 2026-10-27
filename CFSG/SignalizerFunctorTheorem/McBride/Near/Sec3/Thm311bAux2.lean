module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm311bAux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Semisimple
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Back
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleCommutator

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.Nonsolvable (IsASimple)

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm311b

variable {Γ : Type*} [Group Γ]

structure EFSetting (p : ℕ) (A G F E₁ A₁ : Subgroup Γ) (a : Γ) : Prop where
  F_le : F ≤ A
  A₁_le : A₁ ≤ A
  E₁_le : E₁ ≤ A₁
  E₁_eq : E₁ = Subgroup.zpowers a
  card_E₁ : Nat.card E₁ = p
  inf_eq : F ⊓ A₁ = ⊥
  sup_eq : F ⊔ A₁ = A
  F_cen : ∀ J ∈ lcal G, F ≤ Subgroup.centralizer (J : Set Γ)
  a_not_cen : ∀ J ∈ lcal G, a ∉ Subgroup.centralizer (J : Set Γ)
  A₁_norm : ∀ J ∈ lcal G, ∀ x ∈ A₁, x ∈ Subgroup.normalizer (J : Set Γ) → x ∈ E₁

theorem card_eq_mul_of_isCompl {A H K : Subgroup Γ} (hHA : H ≤ A) (hKA : K ≤ A)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hinf : H ⊓ K = ⊥) (hsup : H ⊔ K = A) :
    Nat.card A = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥A := fun x => ⟨(x.1 : Γ) * (x.2 : Γ), mul_mem (hHA x.1.2) (hKA x.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨h, hh⟩, ⟨k, hk⟩⟩ ⟨⟨h', hh'⟩, ⟨k', hk'⟩⟩ hf
    have hf' : h * k = h' * k' := congrArg Subtype.val hf
    have h1 : h'⁻¹ * h = k' * k⁻¹ := by
      calc h'⁻¹ * h = h'⁻¹ * (h * k) * k⁻¹ := by group
        _ = h'⁻¹ * (h' * k') * k⁻¹ := by rw [hf']
        _ = k' * k⁻¹ := by group
    have h2 : h'⁻¹ * h ∈ H ⊓ K :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hh') hh, h1 ▸ mul_mem hk' (inv_mem hk)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    have h3 : k' * k⁻¹ = 1 := by rw [← h1]; group
    rw [mul_inv_eq_one] at h3
    subst h3
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hsup] at hx
    obtain ⟨h, hh, k, hk, rfl⟩ := (mem_sup_iff_of_commute fun h hh k hk =>
      (show Commute h k from hcomm h hh k hk)).mp hx
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm

section Setting

variable [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem exists_efSetting (hyp : Lemma212.Hyp p A G) :
    ∃ (F E₁ A₁ : Subgroup Γ) (a : Γ), EFSetting p A G F E₁ A₁ a := by
  have hp : p.Prime := hyp.near.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨J₀, hJ₀⟩ := hyp.exists_lcal
  obtain ⟨a, haE, haC, hgen⟩ := hyp.exists_generator hJ₀
  set E := A ⊓ Subgroup.normalizer (J₀ : Set Γ) with hE
  set F := A ⊓ Subgroup.centralizer (J₀ : Set Γ) with hF
  have haA : a ∈ A := (Subgroup.mem_inf.mp haE).1
  have ha1 : a ≠ 1 := fun h => haC (h ▸ one_mem _)
  have hordA : orderOf a = p := orderOf_eq_prime (hyp.near.elemAbelian.2 a haA) ha1
  have hFE : F ≤ E := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hEA : E ≤ A := inf_le_left
  obtain ⟨C₀, hC₀A, hEC, hEC'⟩ :=
    Lemma212.exists_complement_of_isElemAbelian hp hyp.near.elemAbelian hEA
  set E₁ := Subgroup.zpowers a with hE₁
  have hE₁E : E₁ ≤ E := Subgroup.zpowers_le.mpr haE
  have hE₁A : E₁ ≤ A := hE₁E.trans hEA
  have hcomm : ∀ {x y : Γ}, x ∈ A → y ∈ A → Commute x y := fun hx hy => hyp.comm hx hy
  have hcardE₁ : Nat.card E₁ = p := by rw [hE₁, Nat.card_zpowers, hordA]
  have hFE₁ : F ⊓ E₁ = ⊥ := by
    have : Fact (Nat.Prime (Nat.card ↥E₁)) := ⟨hcardE₁ ▸ hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((F ⊓ E₁).subgroupOf E₁) with h | h
    · refine eq_bot_iff.mpr fun x hx => ?_
      have hx' : (⟨x, (Subgroup.mem_inf.mp hx).2⟩ : ↥E₁) ∈ (F ⊓ E₁).subgroupOf E₁ := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
    · exfalso
      have : (⟨a, Subgroup.mem_zpowers a⟩ : ↥E₁) ∈ (F ⊓ E₁).subgroupOf E₁ := by rw [h]; trivial
      exact haC (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp this).1).2
  set A₁ := E₁ ⊔ C₀ with hA₁
  have hA₁A : A₁ ≤ A := sup_le hE₁A hC₀A
  have hcomm₁ : ∀ x ∈ E₁, ∀ y ∈ C₀, Commute x y := fun x hx y hy =>
    hcomm (hE₁A hx) (hC₀A hy)
  have hdecomp : ∀ x ∈ A₁, ∃ e ∈ E₁, ∃ c ∈ C₀, e * c = x := fun x hx =>
    (mem_sup_iff_of_commute hcomm₁).mp hx
  refine ⟨F, E₁, A₁, a, ⟨inf_le_left, hA₁A, le_sup_left, hE₁, hcardE₁, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxF, hxA₁⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨e, he, c, hc, rfl⟩ := hdecomp x hxA₁
    have hcE : c ∈ E := by
      have : c = e⁻¹ * (e * c) := by group
      rw [this]
      exact mul_mem (inv_mem (hE₁E he)) (hFE hxF)
    have hc1 : c = 1 := by
      have : c ∈ E ⊓ C₀ := Subgroup.mem_inf.mpr ⟨hcE, hc⟩
      rw [hEC, Subgroup.mem_bot] at this
      exact this
    subst hc1
    have : e * 1 ∈ F ⊓ E₁ := Subgroup.mem_inf.mpr ⟨hxF, by simpa using he⟩
    rw [hFE₁] at this
    exact this
  ·
    refine le_antisymm (sup_le inf_le_left hA₁A) fun x hx => ?_
    rw [← hEC'] at hx
    obtain ⟨e, he, c, hc, rfl⟩ := (mem_sup_iff_of_commute fun x hx y hy =>
      hcomm (hEA hx) (hC₀A hy)).mp hx
    have heF : e ∈ F ⊔ E₁ := hgen e he
    have : e * c ∈ (F ⊔ E₁) ⊔ C₀ := Subgroup.mul_mem_sup heF hc
    rwa [sup_assoc] at this
  · intro J hJ x hx
    exact (hyp.cent_iff hJ₀ hJ (Subgroup.mem_inf.mp hx).1).mpr (Subgroup.mem_inf.mp hx).2
  · intro J hJ haJ
    exact haC ((hyp.cent_iff hJ₀ hJ haA).mp haJ)
  · intro J hJ x hx hxN
    obtain ⟨e, he, c, hc, rfl⟩ := hdecomp x hx
    have hxA : e * c ∈ A := hA₁A hx
    have heN : e ∈ Subgroup.normalizer (J : Set Γ) :=
      (hyp.norm_iff hJ₀ hJ (hE₁A he)).mpr (Subgroup.mem_inf.mp (hE₁E he)).2
    have hcN : c ∈ Subgroup.normalizer (J : Set Γ) := by
      have : c = e⁻¹ * (e * c) := by group
      rw [this]
      exact mul_mem (inv_mem heN) hxN
    have hcE : c ∈ E := Subgroup.mem_inf.mpr ⟨hC₀A hc, (hyp.norm_iff hJ₀ hJ (hC₀A hc)).mp hcN⟩
    have hc1 : c = 1 := by
      have : c ∈ E ⊓ C₀ := Subgroup.mem_inf.mpr ⟨hcE, hc⟩
      rw [hEC, Subgroup.mem_bot] at this
      exact this
    rw [hc1, mul_one]
    exact he

@[expose] def freeFamily (F E₁ A₁ : Subgroup Γ) : Set (Subgroup Γ) :=
  {B | ∃ V : Subgroup Γ, V ≤ A₁ ∧ V ⊓ E₁ = ⊥ ∧ V ⊔ E₁ = A₁ ∧ B = F ⊔ V}

variable {F E₁ A₁ : Subgroup Γ} {a : Γ}

theorem orbitClosure_le_iSup
    (hyp : Lemma212.Hyp p A G) (h : EFSetting p A G F E₁ A₁ a)
    {J : Subgroup Γ} (hJ : J ∈ lcal G) :
    orbitClosure J A ≤ ⨆ B ∈ freeFamily F E₁ A₁, cenIn (kOf G) (B : Set Γ) := by
  have hp : p.Prime := hyp.near.prime
  have hJ' : J ∈ lcal (kOf G) := by rw [hyp.lcal_kOf]; exact hJ
  have hSA := hyp.semisimpleAction.orbit hJ'
  have hXle : orbitClosure J A ≤ kOf G :=
    Lemma212.orbitClosure_le_of_normalizer (hyp.hK.le hJ) hyp.A_le_normalizer
  have hA₁elem : IsElemAbelian p A₁ := Thm32.isElemAbelian_of_le hyp.near.elemAbelian h.A₁_le
  have hAX : Admits A₁ (orbitClosure J A) := h.A₁_le.trans (Thm210.admits_orbitClosure J)
  have hcop : Nat.Coprime p (Nat.card (orbitClosure J A)) :=
    hyp.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (hXle.trans (kOf_le G)))
  have hOut : OutSectionsCyclic p (orbitClosure J A) :=
    outSectionsCyclic_of_isSemisimple hp hSA.semisimple hSA.nearPSolvable
  have hL : IsDirectProduct {K | ∃ b ∈ A, K = J.map (MulAut.conj b).toMonoidHom}
      (orbitClosure J A) := isDirectProduct_orbit hyp.near.admits hJ
  have hD : ∀ D ∈ {K | ∃ b ∈ A, K = J.map (MulAut.conj b).toMonoidHom},
      IsSimpleGroup D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
    rintro _ ⟨b, hb, rfl⟩
    exact Lemma27.simple_of_mem_lcal (hyp.A_perm_lcal hb hJ)
  have htrans : ∀ D ∈ {K | ∃ b ∈ A, K = J.map (MulAut.conj b).toMonoidHom},
      ∀ D' ∈ {K | ∃ b ∈ A, K = J.map (MulAut.conj b).toMonoidHom},
        ∃ c ∈ A₁, D' = D.map (MulAut.conj c).toMonoidHom := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    have hmem : b' * b⁻¹ ∈ F ⊔ A₁ := h.sup_eq ▸ mul_mem hb' (inv_mem hb)
    obtain ⟨f, hf, c, hc, hfc⟩ := (mem_sup_iff_of_commute fun x hx y hy =>
      (show Commute x y from hyp.comm (h.F_le hx) (h.A₁_le hy))).mp hmem
    refine ⟨c, hc, ?_⟩
    have hJb : J.map (MulAut.conj b).toMonoidHom ∈ lcal G := hyp.A_perm_lcal hb hJ
    have hJbc : (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj c).toMonoidHom ∈ lcal G :=
      hyp.A_perm_lcal (h.A₁_le hc) hJb
    have hfix : ((J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj c).toMonoidHom).map
        (MulAut.conj f).toMonoidHom =
        (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj c).toMonoidHom :=
      (Lemma212.mem_normalizer_iff_map_conj _ f).mp
        (Subgroup.centralizer_le_normalizer _ (h.F_cen _ hJbc hf))
    calc J.map (MulAut.conj b').toMonoidHom
        = (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj (b' * b⁻¹)).toMonoidHom := by
          rw [Thm210.map_conj_map_conj, inv_mul_cancel_right]
      _ = (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj (f * c)).toMonoidHom := by
          rw [hfc]
      _ = ((J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj c).toMonoidHom).map
            (MulAut.conj f).toMonoidHom :=
          (Thm210.map_conj_map_conj (J.map (MulAut.conj b).toMonoidHom) c f).symm
      _ = (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj c).toMonoidHom := hfix
  have hAS : IsASimple A₁ (orbitClosure J A) :=
    Lemma27.isASimple_of_isDirectProduct hL hD
      ⟨J, 1, one_mem _, (Thm210.map_conj_one J).symm⟩ hAX htrans
  have hchief : IsChiefFactorOf (orbitClosure J A ⊔ A₁) (orbitClosure J A) ⊥ :=
    isChiefFactorOf_of_isASimple hAS
  rcases eq_or_eq_of_chief hp hA₁elem hAX hcop hOut h.E₁_le hchief with h1 | h2
  · rw [h1]
    refine iSup₂_le fun E' hE' => ?_
    refine le_iSup₂_of_le (F ⊔ E') ⟨E', hE'.1, hE'.2.1, hE'.2.2, rfl⟩ ?_
    intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hXle hxX, ?_⟩
    have hF : F ≤ Subgroup.centralizer ({x} : Set Γ) := by
      intro f hf
      have hfc := Lemma27.centralizer_orbitClosure hyp.near.elemAbelian.1 (h.F_le hf)
        (h.F_cen J hJ hf)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hfc x hxX).symm
    have hE' : E' ≤ Subgroup.centralizer ({x} : Set Γ) := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hxC e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : y ∈ Subgroup.centralizer ({x} : Set Γ) := (sup_le hF hE') hy
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  · exfalso
    have hJle : J ≤ Subgroup.centralizer (E₁ : Set Γ) := fun x hx =>
      (Subgroup.mem_inf.mp (h2 ▸ le_orbitClosure J A hx : x ∈ cenIn (orbitClosure J A)
        (E₁ : Set Γ))).2
    refine h.a_not_cen J hJ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hJle hx) a (h.E₁_eq ▸ Subgroup.mem_zpowers a)).symm

omit [Finite Γ] in
theorem freeFamily_spec {p : ℕ} {A G F E₁ A₁ : Subgroup Γ} {a : Γ} [Finite Γ]
    (hyp : Lemma212.Hyp p A G) (h : EFSetting p A G F E₁ A₁ a) {B : Subgroup Γ}
    (hB : B ∈ freeFamily F E₁ A₁) :
    B ≤ A ∧ Nat.card A = p * Nat.card B ∧
      ∀ J ∈ lcal G, B ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ) := by
  obtain ⟨V, hVA₁, hVE₁, hVsup, rfl⟩ := hB
  have hVA : V ≤ A := hVA₁.trans h.A₁_le
  have hBA : F ⊔ V ≤ A := sup_le h.F_le hVA
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hyp.comm hx hy
  refine ⟨hBA, ?_, ?_⟩
  · have hinf : E₁ ⊓ (F ⊔ V) = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      obtain ⟨hxE₁, hxB⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨f, hf, v, hv, hfv⟩ := (mem_sup_iff_of_commute fun x hx y hy =>
        (show Commute x y from hcommA x (h.F_le hx) y (hVA hy))).mp hxB
      have hfA₁ : f ∈ A₁ := by
        have : f = x * v⁻¹ := by rw [← hfv]; group
        rw [this]
        exact mul_mem (h.E₁_le hxE₁) (inv_mem (hVA₁ hv))
      have hf1 : f = 1 := by
        have : f ∈ F ⊓ A₁ := Subgroup.mem_inf.mpr ⟨hf, hfA₁⟩
        rw [h.inf_eq, Subgroup.mem_bot] at this
        exact this
      subst hf1
      have hxV : x ∈ V := by simpa [← hfv] using hv
      have : x ∈ V ⊓ E₁ := Subgroup.mem_inf.mpr ⟨hxV, hxE₁⟩
      rw [hVE₁, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr this
    have hsup : E₁ ⊔ (F ⊔ V) = A := by
      refine le_antisymm (sup_le (h.E₁_le.trans h.A₁_le) hBA) ?_
      rw [← h.sup_eq, ← hVsup]
      exact sup_le (le_sup_of_le_right le_sup_left) (sup_le (le_sup_of_le_right le_sup_right)
        le_sup_left)
    have := card_eq_mul_of_isCompl (h.E₁_le.trans h.A₁_le) hBA
      (fun x hx y hy => hcommA x (h.E₁_le.trans h.A₁_le hx) y (hBA hy)) hinf hsup
    rwa [h.card_E₁] at this
  · intro J hJ x hx
    obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨f, hf, v, hv, hfv⟩ := (mem_sup_iff_of_commute fun x hx y hy =>
      (show Commute x y from hcommA x (h.F_le hx) y (hVA hy))).mp hxB
    have hfN : f ∈ Subgroup.normalizer (J : Set Γ) :=
      Subgroup.centralizer_le_normalizer _ (h.F_cen J hJ hf)
    have hvN : v ∈ Subgroup.normalizer (J : Set Γ) := by
      have : v = f⁻¹ * x := by rw [← hfv]; group
      rw [this]
      exact mul_mem (inv_mem hfN) hxN
    have hvE₁ : v ∈ E₁ := h.A₁_norm J hJ v (hVA₁ hv) hvN
    have hv1 : v = 1 := by
      have : v ∈ V ⊓ E₁ := Subgroup.mem_inf.mpr ⟨hv, hvE₁⟩
      rw [hVE₁, Subgroup.mem_bot] at this
      exact this
    subst hv1
    rw [mul_one] at hfv
    rw [← hfv]
    exact h.F_cen J hJ hf

theorem exists_free_family (hyp : Lemma212.Hyp p A G) :
    ∃ 𝒰 : Set (Subgroup Γ), 𝒰.Nonempty ∧
      (∀ B ∈ 𝒰, B ≤ A ∧ Nat.card A = p * Nat.card B ∧
        ∀ J ∈ lcal G, B ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) ∧
      kOf G ≤ ⨆ B ∈ 𝒰, cenIn (kOf G) (B : Set Γ) := by
  obtain ⟨F, E₁, A₁, a, h⟩ := exists_efSetting hyp
  refine ⟨freeFamily F E₁ A₁, ?_, fun B hB => freeFamily_spec hyp h hB, ?_⟩
  · obtain ⟨V, hVA₁, hVE₁, hVsup⟩ := Lemma212.exists_complement_of_isElemAbelian hyp.near.prime
      (Thm32.isElemAbelian_of_le hyp.near.elemAbelian h.A₁_le) h.E₁_le
    exact ⟨F ⊔ V, V, hVA₁, by rwa [inf_comm], by rwa [sup_comm], rfl⟩
  · calc kOf G = sSup (lcal G) := hyp.hK.sSup_eq.symm
      _ ≤ _ := sSup_le fun J hJ => (le_orbitClosure J A).trans (orbitClosure_le_iSup hyp h hJ)

end Setting

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm311b
