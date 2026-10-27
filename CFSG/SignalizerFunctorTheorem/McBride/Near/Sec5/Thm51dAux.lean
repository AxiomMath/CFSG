module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.GlaubermanUniv
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Lift
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Restrict

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm51d

variable {p : ℕ} {G : Type u} [Group G] {A : Subgroup G} {θ : G → Subgroup G}

theorem admits_wsub : Admits A (wsub p A θ) := by
  unfold wsub
  rw [sSup_eq_iSup]
  exact Admits.iSup fun X => Admits.iSup fun hX => hX.1

theorem apply_le_wsub (hθ : NearFunctor p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    θ a ≤ wsub p A θ :=
  le_sSup (apply_mem_assoc hθ ha ha1)

theorem wsub_eq_thetaSup [Finite G] (hθ : NearFunctor p A θ) (hrank : p ^ 2 ≤ Nat.card A) :
    wsub p A θ = thetaSup A θ :=
  sSup_signalizers_eq_thetaSup hθ.prime hθ.elemAbelian hrank hθ.isFunctor hθ.near

theorem sq_le_card_of_cube_le (hp : p.Prime) (hrank : p ^ 3 ≤ Nat.card A) :
    p ^ 2 ≤ Nat.card A :=
  (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hrank

@[expose] def omegaCenter (r : ℕ) (W : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ W ∧ z ∈ Subgroup.centralizer (W : Set G) ∧ z ^ r = 1}
  one_mem' := ⟨one_mem _, one_mem _, one_pow r⟩
  mul_mem' := by
    rintro x y ⟨hxW, hxC, hxr⟩ ⟨hyW, hyC, hyr⟩
    refine ⟨mul_mem hxW hyW, mul_mem hxC hyC, ?_⟩
    have hcomm : Commute x y := Subgroup.mem_centralizer_iff.mp hyC x hxW
    rw [hcomm.mul_pow, hxr, hyr, one_mul]
  inv_mem' := by
    rintro x ⟨hxW, hxC, hxr⟩
    exact ⟨inv_mem hxW, inv_mem hxC, by rw [inv_pow, hxr, inv_one]⟩

theorem omegaCenter_le {r : ℕ} {W : Subgroup G} : omegaCenter r W ≤ W := fun _ hz => hz.1

theorem omegaCenter_le_centralizer {r : ℕ} {W : Subgroup G} :
    omegaCenter r W ≤ Subgroup.centralizer (W : Set G) := fun _ hz => hz.2.1

theorem pow_eq_one_of_mem_omegaCenter {r : ℕ} {W : Subgroup G} {z : G}
    (hz : z ∈ omegaCenter r W) : z ^ r = 1 := hz.2.2

theorem normal_omegaCenter {r : ℕ} {W : Subgroup G} (hW : W.Normal) :
    (omegaCenter r W).Normal where
  conj_mem := by
    rintro x ⟨hxW, hxC, hxr⟩ g
    refine ⟨hW.conj_mem x hxW g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : g⁻¹ * w * g ∈ W := by simpa using hW.conj_mem w hw g⁻¹
      have key := Subgroup.mem_centralizer_iff.mp hxC _ hw'
      calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [key]
        _ = (g * x * g⁻¹) * w := by group
    · rw [conj_pow, hxr]
      group

theorem isPGroup_omegaCenter {r : ℕ} {W : Subgroup G} : IsPGroup r (omegaCenter r W) := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using pow_eq_one_of_mem_omegaCenter g.2)⟩

theorem omegaCenter_ne_bot [Finite G] {r : ℕ} (hr : r.Prime) {W : Subgroup G}
    (hdvd : r ∣ Nat.card (W ⊓ Subgroup.centralizer (W : Set G) : Subgroup G)) :
    omegaCenter r W ≠ ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  intro hbot
  have hxmem : (x : G) ∈ omegaCenter r W := by
    refine ⟨x.2.1, x.2.2, ?_⟩
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  rw [hbot, Subgroup.mem_bot] at hxmem
  have : x = 1 := Subtype.ext hxmem
  rw [this, orderOf_one] at hx
  exact hr.one_lt.ne hx

section Quotient

variable [Finite G]

theorem nearASolvable_imageFunctor_apply (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) (hnear : ∀ a ∈ A, a ≠ 1 → NearASolvable p A (θ a))
    {N : Subgroup G} [N.Normal] (hf : Set.InjOn (QuotientGroup.mk' N) A) {x : G ⧸ N}
    (hx : x ∈ A.map (QuotientGroup.mk' N)) (hx1 : x ≠ 1) :
    NearASolvable p (A.map (QuotientGroup.mk' N)) (imageFunctor (QuotientGroup.mk' N) A θ x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  have ha1 : a ≠ 1 := fun h => hx1 (by rw [h, map_one])
  rw [imageFunctor_apply hf ha]
  exact (isSigClass_nearClass.{u} hp).quotient G hA (hθ.normalized a ha ha1)
    (hθ.coprime a ha ha1) (hnear a ha ha1)

theorem isCompleteIn_quotient (h : Counterexample p A θ) {N : Subgroup G} [N.Normal]
    (hN : N ≠ ⊥) (hf : Set.InjOn (QuotientGroup.mk' N) A) :
    IsCompleteIn (signalizers p (A.map (QuotientGroup.mk' N))
      (imageFunctor (QuotientGroup.mk' N) A θ)
      (NearASolvable p (A.map (QuotientGroup.mk' N)))) := by
  have hp := h.hyp.prime
  have hA := h.hyp.elemAbelian
  set π : G →* G ⧸ N := QuotientGroup.mk' N
  have hlt : Nat.card (G ⧸ N) < Nat.card G := by
    have h1 : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hN
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    nlinarith
  have hinj : Function.Injective (π.domRestrict A) := fun x y hxy =>
    Subtype.ext (hf x.2 y.2 hxy)
  have hAe : IsElemAbelian p (A.map π) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_image p π A hA
  have hcard : Nat.card (A.map π) = p ^ 3 := by
    rw [CFSG.SignalizerFunctor.Helpers.subgroup_image_card_of_injective π A hinj, h.hyp.card]
  have hfun := h.hyp.isFunctor.imageFunctor hp hA hf
  exact h.ih (G ⧸ N) hlt (A.map π) (imageFunctor π A θ) ⟨hp, h.hyp.odd, hAe, hcard, hfun,
    fun x hx hx1 => nearASolvable_imageFunctor_apply hp hA h.hyp.isFunctor h.hyp.near hf hx hx1⟩

theorem map_wsub_le (h : Counterexample p A θ) {N : Subgroup G} [N.Normal]
    (hf : Set.InjOn (QuotientGroup.mk' N) A) {Wb : Subgroup (G ⧸ N)}
    (hmax : ∀ X ∈ signalizers p (A.map (QuotientGroup.mk' N))
      (imageFunctor (QuotientGroup.mk' N) A θ)
      (NearASolvable p (A.map (QuotientGroup.mk' N))), X ≤ Wb) :
    (wsub p A θ).map (QuotientGroup.mk' N) ≤ Wb := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine hmax _ (map_mem_signalizers_imageFunctor h.hyp.prime h.hyp.elemAbelian hf hX ?_)
  exact (isSigClass_nearClass.{u} h.hyp.prime).quotient G h.hyp.elemAbelian hX.1 hX.2.1
    hX.2.2.2

theorem coprime_and_fixed_of_normal (h : Counterexample p A θ) {N : Subgroup G} [N.Normal]
    (hN : N ≠ ⊥) (hcop : Nat.Coprime p (Nat.card N)) :
    Nat.Coprime p (Nat.card (wsub p A θ)) ∧
      ∀ a ∈ A, a ≠ 1 → wsub p A θ ⊓ Subgroup.centralizer {a} ≤ θ a ⊔ N := by
  have hp := h.hyp.prime
  have hf : Set.InjOn (QuotientGroup.mk' N) A :=
    injOn_of_coprime_ker hp h.hyp.elemAbelian (by rw [QuotientGroup.ker_mk']; exact hcop)
  obtain ⟨Wb, hWb, hmax⟩ := isCompleteIn_quotient h hN hf
  exact coprime_and_fixed_le_of_map_le hp h.hyp.elemAbelian hcop hWb admits_wsub
    (map_wsub_le h hf hmax)

end Quotient

section Splitting

variable [Finite G]

theorem exists_invariant_complement_of_fixed (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 3 ≤ Nat.card A) (hθ : IsFunctor p A θ) {r : ℕ} (hr : r.Prime)
    {R Z₀ : Subgroup G} (hR : IsPGroup r R) (hpR : Nat.Coprime p (Nat.card R))
    (hAR : Admits A R) (hZR : Z₀ ≤ R) (hAZ : Admits A Z₀)
    (hθZ : ∀ a ∈ A, a ≠ 1 → Admits (θ a) Z₀) (hZθ : ∀ a ∈ A, a ≠ 1 → Z₀ ⊓ θ a = ⊥)
    (hfix : ∀ a ∈ A, a ≠ 1 → R ⊓ Subgroup.centralizer {a} ≤ θ a ⊔ Z₀) :
    ∃ R₁ : Subgroup G, R₁ ≤ R ∧ Admits A R₁ ∧ Z₀ ⊓ R₁ = ⊥ ∧ Z₀ ⊔ R₁ = R := by
  have : Fact r.Prime := ⟨hr⟩
  have hrank2 := sq_le_card_of_cube_le hp hrank
  have hθR : IsFunctor p A (restrictFunctor R θ) := hθ.restrictFunctor hAR
  have hsolR : ∀ a ∈ A, a ≠ 1 → Group.IsSolvable (restrictFunctor R θ a) := by
    intro a ha ha1
    have h1 : IsPGroup r (θ a ⊓ R : Subgroup G) := hR.to_le inf_le_right
    have := h1.isNilpotent
    change Group.IsSolvable ↥(θ a ⊓ R : Subgroup G)
    infer_instance
  obtain ⟨R₁, -, hAR₁, hR₁cop, hR₁fix, -⟩ :=
    exists_greatest_signalizer_of_isFunctor hp hA hrank hθR hsolR
  have hR₁le : R₁ ≤ R := by
    rw [← iSup_centralizer_nonidentity hp hA hrank2 hAR₁ hR₁cop]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    exact (hR₁fix a ha ha1).le.trans (inf_le_right : θ a ⊓ R ≤ R)
  have hdisj : Z₀ ⊓ R₁ = ⊥ := by
    have hAX : Admits A (Z₀ ⊓ R₁) := Admits.inf hAZ hAR₁
    have hXcop : Nat.Coprime p (Nat.card (Z₀ ⊓ R₁ : Subgroup G)) :=
      hR₁cop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
    rw [eq_bot_iff, ← iSup_centralizer_nonidentity hp hA hrank2 hAX hXcop]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    intro x hx
    have hxθ : x ∈ θ a := ((hR₁fix a ha ha1).le ⟨hx.1.2, hx.2⟩).1
    have hmem : x ∈ Z₀ ⊓ θ a := ⟨hx.1.1, hxθ⟩
    rwa [hZθ a ha ha1] at hmem
  refine ⟨R₁, hR₁le, hAR₁, hdisj, le_antisymm (sup_le hZR hR₁le) ?_⟩
  rw [← iSup_centralizer_nonidentity hp hA hrank2 hAR hpR]
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  intro x hx
  have hx' : x ∈ Z₀ ⊔ θ a := by
    rw [sup_comm]
    exact hfix a ha ha1 hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left Z₀ (θ a)
    (hθZ a ha ha1)] at hx'
  obtain ⟨z, hz, t, ht, rfl⟩ := hx'
  have htR : t ∈ R := by
    have := mul_mem (inv_mem (hZR hz)) hx.1
    simpa using this
  have htR₁ : t ∈ R₁ := ((hR₁fix a ha ha1).ge ⟨ht, htR⟩).1
  exact mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right htR₁)

theorem exists_invariant_complement_of_central (hp : p.Prime) (hA : IsElemAbelian p A)
    (hrank : p ^ 3 ≤ Nat.card A) (hθ : IsFunctor p A θ) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p)
    {W Z₀ : Subgroup G} (hWcop : Nat.Coprime p (Nat.card W)) (hAW : Admits A W)
    (hZW : Z₀ ≤ W) (hZc : Z₀ ≤ Subgroup.centralizer (W : Set G)) (hAZ : Admits A Z₀)
    (hZr : IsPGroup r Z₀) (hθW : ∀ a ∈ A, a ≠ 1 → θ a ≤ W)
    (hZθ : ∀ a ∈ A, a ≠ 1 → Z₀ ⊓ θ a = ⊥)
    (hfix : ∀ a ∈ A, a ≠ 1 → W ⊓ Subgroup.centralizer {a} ≤ θ a ⊔ Z₀) :
    ∃ W₀ : Subgroup G, W₀ ≤ W ∧ Admits A W₀ ∧ Z₀ ⊓ W₀ = ⊥ ∧ Z₀ ⊔ W₀ = W := by
  have : Fact r.Prime := ⟨hr⟩
  have hApG : IsPGroup p A := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA
  have hWZ : W ≤ Subgroup.normalizer (Z₀ : Set G) :=
    (Subgroup.le_centralizer_iff.mp hZc).trans (Subgroup.centralizer_le_normalizer _)
  have hcomm : IsMulCommutative Z₀ :=
    ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp (hZc y.2) x (hZW x.2))⟩⟩
  obtain ⟨P, hP⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow p r hp hr
    A W hApG hAW hWcop
  set R : Subgroup G := (P : Subgroup W).map W.subtype with hRdef
  have hRW : R ≤ W := Subgroup.map_subtype_le _
  have hRr : IsPGroup r R := P.isPGroup'.map W.subtype
  have hRcop : Nat.Coprime p (Nat.card R) :=
    hWcop.coprime_dvd_right (Subgroup.card_dvd_of_le hRW)
  have hZP : Z₀.subgroupOf W ≤ (P : Subgroup W) := by
    have hnorm : (Z₀.subgroupOf W).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hZW).mpr hWZ
    have hZp' : IsPGroup r (Z₀.subgroupOf W) := hZr.comap_subtype
    exact IsPGroup.le_sylow_of_normal hZp' P
  have hZR : Z₀ ≤ R := fun z hz => ⟨⟨z, hZW hz⟩, hZP hz, rfl⟩
  have hθZ : ∀ a ∈ A, a ≠ 1 → Admits (θ a) Z₀ := fun a ha ha1 => (hθW a ha ha1).trans hWZ
  obtain ⟨R₁, hR₁R, -, hdisj, hsup⟩ := exists_invariant_complement_of_fixed hp hA hrank hθ hr
    hRr hRcop hP hZR hAZ hθZ hZθ (fun a ha ha1 => (inf_le_inf_right _ hRW).trans (hfix a ha ha1))
  have hNK : Z₀.subgroupOf W ⊓ R₁.subgroupOf W = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have hx' : (x : G) ∈ Z₀ ⊓ R₁ := hx
    rw [hdisj, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have hNsup : Z₀.subgroupOf W ⊔ R₁.subgroupOf W = (P : Subgroup W) := by
    rw [← Subgroup.subgroupOf_sup hZW (hR₁R.trans hRW), hsup, hRdef]
    exact Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
  exact exists_invariant_complement hp hr hrp.symm hApG hWcop hAW hZW hZr hWZ hAZ P hZP hNK
    hNsup

end Splitting

section NeCase

variable [Finite G]

theorem false_of_complement (h : Counterexample p A θ)
    (hsol : ∃ a ∈ A, a ≠ 1 ∧ ¬ Group.IsSolvable (θ a))
    (hnormal : ∀ N : Subgroup G, N.Normal → N ∈ assoc p A θ → N = ⊥)
    (hG : wsub p A θ ⊔ A = ⊤) {Z₀ W₀ : Subgroup G} [Z₀.Normal] (hZbot : Z₀ ≠ ⊥)
    (hZW : Z₀ ≤ wsub p A θ) (hZc : Z₀ ≤ Subgroup.centralizer (wsub p A θ : Set G))
    (hW₀W : W₀ ≤ wsub p A θ) (hAW₀ : Admits A W₀) (hdisj : Z₀ ⊓ W₀ = ⊥)
    (hsup : Z₀ ⊔ W₀ = wsub p A θ) : False := by
  have hθ := h.hyp.nearFunctor
  have hp := h.hyp.prime
  have hA := h.hyp.elemAbelian
  have hrank3 : p ^ 3 ≤ Nat.card A := h.hyp.card.ge
  have hrank2 := sq_le_card_of_cube_le hp hrank3
  have hcen : ∀ z ∈ Z₀, ∀ w ∈ wsub p A θ, w * z = z * w := fun z hz w hw =>
    Subgroup.mem_centralizer_iff.mp (hZc hz) w hw
  have hWN : wsub p A θ ≤ Subgroup.normalizer (W₀ : Set G) := by
    rw [← hsup]
    refine sup_le ?_ Subgroup.le_normalizer
    rw [Subgroup.le_normalizer_iff]
    intro z hz k hk
    have : z * k * z⁻¹ = k := by
      rw [← hcen z hz k (hW₀W hk), mul_assoc, mul_inv_cancel, mul_one]
    rwa [this]
  set θ₀ : G → Subgroup G := restrictFunctor W₀ θ
  have hθ₀fun : IsFunctor p A θ₀ := h.hyp.isFunctor.restrictFunctor hAW₀
  have hθ₀near : ∀ a ∈ A, a ≠ 1 → NearASolvable p A (θ₀ a) := fun a ha ha1 =>
    nearASolvable_of_le hp (h.hyp.near a ha ha1) inf_le_left
      (Admits.inf (h.hyp.isFunctor.normalized a ha ha1) hAW₀)
  have hnh : NearHyp p A θ₀ := ⟨hp, h.hyp.odd, hA, h.hyp.card, hθ₀fun, hθ₀near⟩
  have hex : ∃ a ∈ A, a ≠ 1 ∧ ¬ θ a ≤ W₀ := by
    by_contra hcon
    push Not at hcon
    have hW_le : wsub p A θ ≤ W₀ := by
      rw [wsub_eq_thetaSup hθ hrank2]
      exact thetaSup_le hcon
    exact hZbot (eq_bot_iff.mpr ((le_inf le_rfl (hZW.trans hW_le)).trans hdisj.le))
  obtain ⟨V, hV, hVmax⟩ := h.complete_of_size_lt hnh (size_restrictFunctor_lt hex)
  have hVB : ∀ B : Subgroup G, B ≤ A → p ^ 2 ≤ Nat.card B → thetaSup B θ₀ = V := by
    intro B hBA hB2
    refine le_antisymm (thetaSup_le fun b hb hb1 => ?_)
      (le_thetaSup_of_mem_signalizers hp hA hBA hB2 hV)
    exact hVmax _ (hθ₀fun.apply_mem_signalizers (hBA hb) hb1 (hθ₀near b (hBA hb) hb1))
  have hHB : ∀ B : Subgroup G, B ≤ A → p ^ 2 ≤ Nat.card B →
      thetaOf θ B ≤ Subgroup.normalizer (V : Set G) := by
    intro B hBA hB2
    rw [← hVB B hBA hB2]
    unfold thetaSup
    refine Admits.iSup fun a => Admits.iSup fun ha => Admits.iSup fun ha1 => ?_
    have hθa : θ a ≤ Subgroup.normalizer (W₀ : Set G) :=
      (apply_le_wsub hθ (hBA ha) ha1).trans hWN
    exact (thetaOf_le_apply ha ha1).trans (Admits.inf (admits_self (θ a)) hθa)
  have hθV : ∀ a ∈ A, a ≠ 1 → θ a ≤ Subgroup.normalizer (V : Set G) := by
    intro a ha ha1
    rw [h.hyp.isFunctor.apply_eq_iSup_thetaOf hp hA hrank3 ha ha1]
    refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hBc => iSup_le fun haB => ?_
    exact hHB B hBA hBc.ge
  have hWV : wsub p A θ ≤ Subgroup.normalizer (V : Set G) := by
    rw [wsub_eq_thetaSup hθ hrank2]
    exact thetaSup_le hθV
  have hnorm : Subgroup.normalizer (V : Set G) = ⊤ := by
    rw [eq_top_iff, ← hG]
    exact sup_le hWV hV.1
  have hVnormal : V.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  have hVθ : V ∈ assoc p A θ := signalizers_mono_functor (fun a _ _ => inf_le_left) hV
  have hV0 : V = ⊥ := hnormal V hVnormal hVθ
  have hθ₀bot : ∀ a ∈ A, a ≠ 1 → θ a ⊓ W₀ = ⊥ := by
    intro a ha ha1
    have hle := hVmax _ (hθ₀fun.apply_mem_signalizers ha ha1 (hθ₀near a ha ha1))
    rw [hV0] at hle
    exact le_bot_iff.mp hle
  obtain ⟨a, ha, ha1, hns⟩ := hsol
  apply hns
  have hθaW : θ a ≤ wsub p A θ := apply_le_wsub hθ ha ha1
  refine Group.isSolvable_of_comm fun x y => ?_
  have hxW : (x : G) ∈ Z₀ ⊔ W₀ := by
    rw [hsup]
    exact hθaW x.2
  have hyW : (y : G) ∈ Z₀ ⊔ W₀ := by
    rw [hsup]
    exact hθaW y.2
  obtain ⟨z₁, hz₁, w₁, hw₁, hx⟩ := Subgroup.mem_sup_of_normal_left.mp hxW
  obtain ⟨z₂, hz₂, w₂, hw₂, hy⟩ := Subgroup.mem_sup_of_normal_left.mp hyW
  have e1 : (x : G) * y = (z₁ * z₂) * (w₁ * w₂) := by
    rw [← hx, ← hy]
    calc z₁ * w₁ * (z₂ * w₂) = z₁ * (w₁ * z₂) * w₂ := by group
      _ = z₁ * (z₂ * w₁) * w₂ := by rw [hcen z₂ hz₂ w₁ (hW₀W hw₁)]
      _ = (z₁ * z₂) * (w₁ * w₂) := by group
  have e2 : (y : G) * x = (z₁ * z₂) * (w₂ * w₁) := by
    rw [← hx, ← hy]
    calc z₂ * w₂ * (z₁ * w₁) = z₂ * (w₂ * z₁) * w₁ := by group
      _ = z₂ * (z₁ * w₂) * w₁ := by rw [hcen z₁ hz₁ w₂ (hW₀W hw₂)]
      _ = (z₂ * z₁) * (w₂ * w₁) := by group
      _ = (z₁ * z₂) * (w₂ * w₁) := by rw [hcen z₁ hz₁ z₂ (hZW hz₂)]
  have hcW₀ : (w₂ * w₁)⁻¹ * (w₁ * w₂) ∈ W₀ :=
    mul_mem (inv_mem (mul_mem hw₂ hw₁)) (mul_mem hw₁ hw₂)
  have hcθ : ((y : G) * x)⁻¹ * (x * y) ∈ θ a :=
    mul_mem (inv_mem (mul_mem y.2 x.2)) (mul_mem x.2 y.2)
  have hceq : ((y : G) * x)⁻¹ * (x * y) = (w₂ * w₁)⁻¹ * (w₁ * w₂) := by
    rw [e1, e2]
    group
  have hmem : ((y : G) * x)⁻¹ * (x * y) ∈ θ a ⊓ W₀ := ⟨hcθ, hceq ▸ hcW₀⟩
  rw [hθ₀bot a ha ha1, Subgroup.mem_bot] at hmem
  exact Subtype.ext (inv_mul_eq_one.mp hmem).symm

theorem false_of_central_ne (h : Counterexample p A θ)
    (hsol : ∃ a ∈ A, a ≠ 1 ∧ ¬ Group.IsSolvable (θ a))
    (hnormal : ∀ N : Subgroup G, N.Normal → N ∈ assoc p A θ → N = ⊥)
    (hG : wsub p A θ ⊔ A = ⊤) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) {Z₀ : Subgroup G}
    [Z₀.Normal] (hZbot : Z₀ ≠ ⊥) (hZW : Z₀ ≤ wsub p A θ)
    (hZc : Z₀ ≤ Subgroup.centralizer (wsub p A θ : Set G)) (hZr : IsPGroup r Z₀) : False := by
  have hθ := h.hyp.nearFunctor
  have hp := h.hyp.prime
  have hA := h.hyp.elemAbelian
  have hrank3 : p ^ 3 ≤ Nat.card A := h.hyp.card.ge
  have : Fact r.Prime := ⟨hr⟩
  have hZcop : Nat.Coprime p (Nat.card Z₀) := by
    obtain ⟨n, hn⟩ := hZr.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hr).2 hrp.symm)
  obtain ⟨hWcop, hfix⟩ := coprime_and_fixed_of_normal h hZbot hZcop
  have hZn : Subgroup.normalizer (Z₀ : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hAZ : Admits A Z₀ := by
    rw [Admits, hZn]
    exact le_top
  have hZθ : ∀ a ∈ A, a ≠ 1 → Z₀ ⊓ θ a = ⊥ := by
    intro a ha ha1
    have hAN : Admits A (Z₀ ⊓ θ a) := Admits.inf hAZ (h.hyp.isFunctor.normalized a ha ha1)
    have hWN : Admits (wsub p A θ) (Z₀ ⊓ θ a) :=
      (Subgroup.le_centralizer_iff.mp (inf_le_left.trans hZc)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hnormN : Subgroup.normalizer ((Z₀ ⊓ θ a : Subgroup G) : Set G) = ⊤ := by
      rw [eq_top_iff, ← hG]
      exact sup_le hWN hAN
    have hNnormal : (Z₀ ⊓ θ a).Normal := Subgroup.normalizer_eq_top_iff.mp hnormN
    have hNcop : Nat.Coprime p (Nat.card (Z₀ ⊓ θ a : Subgroup G)) :=
      hZcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    have hNmem : (Z₀ ⊓ θ a) ∈ assoc p A θ := by
      refine mem_assoc_iff.mpr ⟨hAN, hNcop, fun b hb hb1 => ?_,
        nearASolvable_of_isPGroup hr hp hrp (hZr.to_le inf_le_left)⟩
      exact (inf_le_inf_right _ inf_le_right).trans (h.hyp.isFunctor.balance a ha ha1 b hb hb1)
    exact hnormal _ hNnormal hNmem
  obtain ⟨W₀, hW₀W, hAW₀, hdisj, hsup⟩ := exists_invariant_complement_of_central hp hA hrank3
    hθ.isFunctor hr hrp hWcop admits_wsub hZW hZc hAZ hZr
    (fun a ha ha1 => apply_le_wsub hθ ha ha1) hZθ hfix
  exact false_of_complement h hsol hnormal hG hZbot hZW hZc hW₀W hAW₀ hdisj hsup

end NeCase

section PCase

variable [Finite G]

theorem exists_complement_of_central_p (hp : p.Prime) {W Z₀ : Subgroup G} [Z₀.Normal]
    (hZW : Z₀ ≤ W) (hZc : Z₀ ≤ Subgroup.centralizer (W : Set G)) (hZp : IsPGroup p Z₀)
    (hcop : Nat.Coprime p (Nat.card (W.map (QuotientGroup.mk' Z₀)))) :
    ∃ K : Subgroup G, K ≤ W ∧ Z₀ ⊓ K = ⊥ ∧ ∀ x ∈ W, Nat.Coprime p (orderOf x) → x ∈ K := by
  have : Fact p.Prime := ⟨hp⟩
  set π : G →* G ⧸ Z₀ := QuotientGroup.mk' Z₀
  have hker : (π.domRestrict W).ker = Z₀.subgroupOf W := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have hcardW : Nat.card (Z₀.subgroupOf W) * Nat.card (W.map π) = Nat.card W := by
    have := Subgroup.card_ker_mul_card_range (π.domRestrict W)
    rwa [hker, MonoidHom.domRestrict_range] at this
  have hindex : (Z₀.subgroupOf W).index = Nat.card (W.map π) := by
    have h1 := Subgroup.card_mul_index (Z₀.subgroupOf W)
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hcardW.symm)
  obtain ⟨n, hn⟩ := hZp.exists_card_eq
  have hNcard : Nat.card (Z₀.subgroupOf W) = Nat.card Z₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
  have hSZ : Nat.Coprime (Nat.card (Z₀.subgroupOf W)) (Z₀.subgroupOf W).index := by
    rw [hindex, hNcard, hn]
    exact Nat.Coprime.pow_left n hcop
  have hnormN : (Z₀.subgroupOf W).Normal := inferInstance
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hSZ
  refine ⟨K.map W.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
    obtain ⟨hzZ, k, hk, rfl⟩ := hz
    have hkN : k ∈ Z₀.subgroupOf W := hzZ
    have hk1 : k = 1 := Subgroup.disjoint_def.mp hK.disjoint hkN hk
    simp [hk1]
  · intro x hxW hxo
    have hmem : (⟨x, hxW⟩ : W) ∈ Z₀.subgroupOf W ⊔ K := by
      rw [hK.sup_eq_top]
      trivial
    obtain ⟨m, hm, k, hk, hmk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hcomm : Commute m k :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hZc hm) k.1 k.2).symm
    have hxo' : Nat.Coprime p (orderOf (⟨x, hxW⟩ : W)) := by
      rw [← Subgroup.orderOf_coe]
      exact hxo
    set o := orderOf (⟨x, hxW⟩ : W)
    have hpow : (m * k) ^ o = 1 := by
      rw [hmk]
      exact pow_orderOf_eq_one _
    have hmo : m ^ o = 1 := by
      rw [hcomm.mul_pow] at hpow
      have h1 : m ^ o = (k ^ o)⁻¹ := eq_inv_of_mul_eq_one_left hpow
      have h2 : m ^ o ∈ Z₀.subgroupOf W := pow_mem hm o
      have h3 : m ^ o ∈ K := by
        rw [h1]
        exact inv_mem (pow_mem hk o)
      exact Subgroup.disjoint_def.mp hK.disjoint h2 h3
    obtain ⟨j, hj⟩ : ∃ j, m ^ p ^ j = 1 := by
      obtain ⟨j, hj⟩ := hZp ⟨m.1, hm⟩
      exact ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
    have hmord : orderOf m = 1 := by
      have h1 : orderOf m ∣ o := orderOf_dvd_of_pow_eq_one hmo
      have h2 : orderOf m ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
      have h3 : Nat.Coprime (orderOf m) o := (Nat.Coprime.pow_left j hxo').coprime_dvd_left h2
      exact h3.eq_one_of_dvd h1
    have hm1 : m = 1 := orderOf_eq_one_iff.mp hmord
    rw [hm1, one_mul] at hmk
    exact ⟨k, hk, congrArg Subtype.val hmk⟩

theorem false_of_central_p (h : Counterexample p A θ) {Z₀ : Subgroup G} [Z₀.Normal]
    (hZbot : Z₀ ≠ ⊥) (hZW : Z₀ ≤ wsub p A θ)
    (hZc : Z₀ ≤ Subgroup.centralizer (wsub p A θ : Set G)) (hZp : IsPGroup p Z₀) : False := by
  have hθ := h.hyp.nearFunctor
  have hp := h.hyp.prime
  have hrank3 : p ^ 3 ≤ Nat.card A := h.hyp.card.ge
  have hrank2 := sq_le_card_of_cube_le hp hrank3
  have hZA : ∀ z ∈ Z₀, z ∈ A → z = 1 := by
    intro z hz hzA
    by_contra hz1
    have hle : ∀ a ∈ A, a ≠ 1 → θ a ≤ θ z := by
      intro a ha ha1 t ht
      have htW : t ∈ wsub p A θ := apply_le_wsub hθ ha ha1 ht
      have htz : t ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp (hZc hz) t htW).symm
      exact h.hyp.isFunctor.balance a ha ha1 z hzA hz1 ⟨ht, htz⟩
    have hWle : wsub p A θ ≤ θ z := by
      rw [wsub_eq_thetaSup hθ hrank2]
      exact thetaSup_le hle
    have hzθ : z ∈ θ z := hWle (hZW hz)
    obtain ⟨k, hk⟩ : ∃ k, orderOf z ∣ p ^ k := by
      obtain ⟨k, hk⟩ := hZp ⟨z, hz⟩
      exact ⟨k, orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)⟩
    have hpd : p ∣ orderOf z := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hk
      rcases j with _ | j
      · exact absurd (orderOf_eq_one_iff.mp (by simpa using hj)) hz1
      · rw [hj]
        exact dvd_pow_self p (Nat.succ_ne_zero j)
    have hdvd : p ∣ Nat.card (θ z) := hpd.trans (Subgroup.orderOf_dvd_natCard _ hzθ)
    exact hp.one_lt.ne' ((h.hyp.isFunctor.coprime z hzA hz1).eq_one_of_dvd hdvd)
  have hf : Set.InjOn (QuotientGroup.mk' Z₀) A := by
    intro a ha b hb hab
    have hab' : (a : G ⧸ Z₀) = b := hab
    have h1 : a⁻¹ * b ∈ Z₀ := QuotientGroup.eq.mp hab'
    exact inv_mul_eq_one.mp (hZA _ h1 (mul_mem (inv_mem ha) hb))
  obtain ⟨Wb, hWb, hmax⟩ := isCompleteIn_quotient h hZbot hf
  have hY := map_wsub_le h hf hmax
  have himcop : Nat.Coprime p (Nat.card ((wsub p A θ).map (QuotientGroup.mk' Z₀))) :=
    hWb.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hY)
  obtain ⟨K, -, hKZ, hKord⟩ := exists_complement_of_central_p hp hZW hZc hZp himcop
  have hle : wsub p A θ ≤ K := by
    refine sSup_le fun X hX x hx => hKord x (le_sSup hX hx) ?_
    exact hX.2.1.coprime_dvd_right (Subgroup.orderOf_dvd_natCard X hx)
  exact hZbot (eq_bot_iff.mpr ((le_inf le_rfl (hZW.trans hle)).trans hKZ.le))

end PCase

end Thm51d

end CFSG.SignalizerFunctorTheorem.McBride.Near
