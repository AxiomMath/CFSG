module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBTwist
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

private def ActCoord {G : Type} [Group G] {k m : ℕ} (V : Subgroup G)
    (β : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)) (l : G)
    (M : Matrix (Fin m) (Fin m) (ZMod 2)) : Prop :=
  ∀ u v : ↥V, (v : G) = l * u * l⁻¹ → ∀ i : Fin k,
    Multiplicative.toAdd (β v) i = M.mulVec (Multiplicative.toAdd (β u) i)

private theorem le_normalizer_commutator_nsb31 {G : Type} [Group G] {N A B : Subgroup G}
    (hA : N ≤ Subgroup.normalizer (A : Set G)) (hB : N ≤ Subgroup.normalizer (B : Set G)) :
    N ≤ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro h hh _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  have key : h * ⁅g₁, g₂⁆ * h⁻¹ = ⁅h * g₁ * h⁻¹, h * g₂ * h⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [key]
  exact Subgroup.commutator_mem_commutator
    ((Subgroup.mem_normalizer_iff.mp (hA hh) g₁).mp hg₁)
    ((Subgroup.mem_normalizer_iff.mp (hB hh) g₂).mp hg₂)

private theorem actCoord_unique_nsb31 {G : Type} [Group G] {k m : ℕ} {V : Subgroup G}
    {β : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)} (hβs : Function.Surjective β)
    (i0 : Fin k) {l : G} (hlV : ∀ x ∈ V, l * x * l⁻¹ ∈ V)
    {M M' : Matrix (Fin m) (Fin m) (ZMod 2)} (hM : ActCoord V β l M)
    (hM' : ActCoord V β l M') : M = M' := by
  have key : ∀ w : Fin m → ZMod 2, M.mulVec w = M'.mulVec w := by
    intro w
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single i0 w : Fin k → Fin m → ZMod 2))
    have hui : Multiplicative.toAdd (β u) i0 = w := by
      rw [hu]
      simp
    have hv : l * (u : G) * l⁻¹ ∈ V := hlV _ u.2
    have h1 := hM u ⟨l * (u : G) * l⁻¹, hv⟩ rfl i0
    have h2 := hM' u ⟨l * (u : G) * l⁻¹, hv⟩ rfl i0
    rw [hui] at h1 h2
    exact h1.symm.trans h2
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  simpa [Matrix.toLin'_apply] using key w

private theorem actCoord_mul_nsb31 {G : Type} [Group G] {k m : ℕ} {V : Subgroup G}
    {β : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)} {l l' : G}
    (hl'V : ∀ x ∈ V, l' * x * l'⁻¹ ∈ V) {M M' : Matrix (Fin m) (Fin m) (ZMod 2)}
    (hM : ActCoord V β l M) (hM' : ActCoord V β l' M') :
    ActCoord V β (l * l') (M * M') := by
  intro u v huv i
  have hw : l' * (u : G) * l'⁻¹ ∈ V := hl'V _ u.2
  have h1 := hM' u ⟨l' * (u : G) * l'⁻¹, hw⟩ rfl i
  have h2 := hM ⟨l' * (u : G) * l'⁻¹, hw⟩ v (by
    rw [huv]
    show l * l' * (u : G) * (l * l')⁻¹ = l * (l' * (u : G) * l'⁻¹) * l⁻¹
    group) i
  rw [h2, h1, Matrix.mulVec_mulVec]

private theorem exists_hom_nsb31 {G : Type} [Group G] {k m : ℕ} (i0 : Fin k) {L V : Subgroup G}
    {β : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)} (hβs : Function.Surjective β)
    (hLV : ∀ l ∈ L, ∀ x ∈ V, l * x * l⁻¹ ∈ V)
    (hex : ∀ l ∈ L, ∃ X : Matrix.GeneralLinearGroup (Fin m) (ZMod 2),
      ActCoord V β l (X : Matrix (Fin m) (Fin m) (ZMod 2))) :
    ∃ ρ : ↥L →* Matrix.GeneralLinearGroup (Fin m) (ZMod 2),
      ∀ l : ↥L, ActCoord V β (l : G) (ρ l : Matrix (Fin m) (Fin m) (ZMod 2)) := by
  choose X hX using hex
  have hmul : ∀ a b : ↥L,
      X ((a * b : ↥L) : G) (L.mul_mem a.2 b.2) = X a a.2 * X b b.2 := by
    intro a b
    have h2 : ActCoord V β ((a * b : ↥L) : G)
        ((X a a.2 * X b b.2 : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) := by
      rw [Units.val_mul]
      exact actCoord_mul_nsb31 (hLV _ b.2) (hX _ a.2) (hX _ b.2)
    exact Units.ext (actCoord_unique_nsb31 hβs i0 (hLV _ (L.mul_mem a.2 b.2))
      (hX _ (L.mul_mem a.2 b.2)) h2)
  exact ⟨MonoidHom.mk' (fun l : ↥L => X l l.2) (fun a b => hmul a b), fun l => hX l l.2⟩

private theorem centralizer_of_actCoord_one_nsb31 {G : Type} [Group G] {k m : ℕ} {V : Subgroup G}
    {β : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)} (hβi : Function.Injective β) {g : G}
    (hgV : ∀ x ∈ V, g * x * g⁻¹ ∈ V) (h : ActCoord V β g 1) :
    g ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hw : Multiplicative.toAdd (β ⟨g * x * g⁻¹, hgV x hx⟩) =
      Multiplicative.toAdd (β ⟨x, hx⟩) := by
    funext i
    rw [h ⟨x, hx⟩ ⟨g * x * g⁻¹, hgV x hx⟩ rfl i, Matrix.one_mulVec]
  have hw' : (⟨g * x * g⁻¹, hgV x hx⟩ : ↥V) = ⟨x, hx⟩ :=
    hβi (Multiplicative.toAdd.injective hw)
  have e : g * x * g⁻¹ = x := congrArg Subtype.val hw'
  calc x * g = g * x * g⁻¹ * g := by rw [e]
    _ = g * x := by group

private def conjEquiv_nsb31 {G : Type} [Group G] {V : Subgroup G} {t : G}
    (ht : ∀ x ∈ V, t * x * t⁻¹ ∈ V) (ht' : ∀ x ∈ V, t⁻¹ * x * t⁻¹⁻¹ ∈ V) : ↥V ≃* ↥V where
  toFun v := ⟨t * (v : G) * t⁻¹, ht (v : G) v.2⟩
  invFun v := ⟨t⁻¹ * (v : G) * t⁻¹⁻¹, ht' (v : G) v.2⟩
  left_inv v := Subtype.ext (show t⁻¹ * (t * (v : G) * t⁻¹) * t⁻¹⁻¹ = v by group)
  right_inv v := Subtype.ext (show t * (t⁻¹ * (v : G) * t⁻¹⁻¹) * t⁻¹ = v by group)
  map_mul' a b := Subtype.ext
    (show t * ((a : G) * (b : G)) * t⁻¹ = (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) by group)

private theorem exists_coordEquiv_nsb31 {G : Type} [Group G] {k m : ℕ} {V : Subgroup G}
    {β : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)} (hβs : Function.Surjective β)
    (hβi : Function.Injective β) (τ : ↥V ≃* ↥V) :
    ∃ Φ : (Fin k → Fin m → ZMod 2) ≃+ (Fin k → Fin m → ZMod 2),
      ∀ v : ↥V, Φ (Multiplicative.toAdd (β v)) = Multiplicative.toAdd (β (τ v)) := by
  obtain ⟨e, he⟩ : ∃ e : ↥V ≃* Multiplicative (Fin k → Fin m → ZMod 2),
      ∀ v : ↥V, e v = β v :=
    ⟨MulEquiv.ofBijective β ⟨hβi, hβs⟩, fun v => rfl⟩
  refine ⟨{ toFun := fun x => Multiplicative.toAdd (e (τ (e.symm (Multiplicative.ofAdd x))))
            invFun := fun x => Multiplicative.toAdd (e (τ.symm (e.symm (Multiplicative.ofAdd x))))
            left_inv := fun x => by simp
            right_inv := fun x => by simp
            map_add' := fun x y => by simp }, fun v => ?_⟩
  have hv : e.symm (β v) = v := by
    rw [← he v]
    exact e.symm_apply_apply v
  show Multiplicative.toAdd (e (τ (e.symm (β v)))) = Multiplicative.toAdd (β (τ v))
  rw [hv, he]

private theorem core_nsb31 {G : Type} [Group G] {k m : ℕ} (hm : 0 < m) (hk : 0 < k)
    {T L V : Subgroup G} {β : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)}
    (hβs : Function.Surjective β) (hβi : Function.Injective β)
    (hLV : ∀ l ∈ L, ∀ x ∈ V, l * x * l⁻¹ ∈ V)
    (hTV : ∀ t ∈ T, ∀ x ∈ V, t * x * t⁻¹ ∈ V)
    (hTL : ∀ t ∈ T, ∀ x ∈ L, t * x * t⁻¹ ∈ L)
    (hex : ∀ l ∈ L, ∃ X : Matrix.GeneralLinearGroup (Fin m) (ZMod 2),
      ActCoord V β l (X : Matrix (Fin m) (Fin m) (ZMod 2)))
    (hsurj : ∀ g : Matrix.GeneralLinearGroup (Fin m) (ZMod 2), ∃ l ∈ L,
      ActCoord V β l (g : Matrix (Fin m) (Fin m) (ZMod 2)))
    {t : G} (ht : t ∈ T) :
    ∃ p ∈ L, ∀ l ∈ L,
      (p⁻¹ * t) * l * (p⁻¹ * t)⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨ρ, hρ⟩ := exists_hom_nsb31 (⟨0, hk⟩ : Fin k) hβs hLV hex
  have hρs : Function.Surjective ρ := by
    intro g
    obtain ⟨l, hl, hact⟩ := hsurj g
    refine ⟨⟨l, hl⟩, Units.ext ?_⟩
    exact actCoord_unique_nsb31 hβs (⟨0, hk⟩ : Fin k) (hLV l hl) (hρ ⟨l, hl⟩) hact
  obtain ⟨conjT, hconjT⟩ : ∃ c : ↥L →* ↥L, ∀ x : ↥L, (c x : G) = t * (x : G) * t⁻¹ :=
    ⟨MonoidHom.mk' (fun x : ↥L => ⟨t * (x : G) * t⁻¹, hTL t ht x x.2⟩)
      (fun a b => Subtype.ext
        (show t * ((a : G) * (b : G)) * t⁻¹ = (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) by
          group)),
      fun x => rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ↥V ≃* ↥V, ∀ v : ↥V, (τ v : G) = t * (v : G) * t⁻¹ :=
    ⟨conjEquiv_nsb31 (fun x hx => hTV t ht x hx) (fun x hx => hTV t⁻¹ (T.inv_mem ht) x hx),
      fun v => rfl⟩
  obtain ⟨Φ, hΦv⟩ := exists_coordEquiv_nsb31 hβs hβi τ
  have hΦ : ∀ (x : ↥L) (u : Fin k → Fin m → ZMod 2) (i : Fin k),
      Φ (fun j => (ρ x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (u j)) i =
        ((ρ.comp conjT) x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (Φ u i) := by
    intro x u i
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd u)
    have hwu : Multiplicative.toAdd (β w) = u := by
      simp [hw]
    have hwV : (x : G) * (w : G) * (x : G)⁻¹ ∈ V := hLV x x.2 w w.2
    have hfun : (fun j => (ρ x : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (u j)) =
        Multiplicative.toAdd (β ⟨(x : G) * (w : G) * (x : G)⁻¹, hwV⟩) := by
      funext j
      rw [hρ x w ⟨(x : G) * (w : G) * (x : G)⁻¹, hwV⟩ rfl j, hwu]
    have hΦu : Φ u = Multiplicative.toAdd (β (τ w)) := by
      rw [← hwu, hΦv]
    have hcomp : ((τ ⟨(x : G) * (w : G) * (x : G)⁻¹, hwV⟩ : ↥V) : G) =
        ((conjT x : ↥L) : G) * ((τ w : ↥V) : G) * ((conjT x : ↥L) : G)⁻¹ := by
      simp only [hτ, hconjT]
      group
    rw [hfun, hΦv, hΦu]
    exact hρ (conjT x) (τ w) (τ ⟨(x : G) * (w : G) * (x : G)⁻¹, hwV⟩) hcomp i
  obtain ⟨P, hP⟩ := natural_twist hm hk ρ (ρ.comp conjT) hρs Φ hΦ
  obtain ⟨p', hp'⟩ := hρs P
  refine ⟨(p' : G), p'.2, fun l hl => ?_⟩
  have h1 : ρ (conjT ⟨l, hl⟩) = P * ρ ⟨l, hl⟩ * P⁻¹ := hP ⟨l, hl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ↥L, g = p'⁻¹ * conjT ⟨l, hl⟩ * p' * ⟨l, hl⟩⁻¹ := ⟨_, rfl⟩
  have hgρ : ρ g = 1 := by
    rw [hgdef]
    simp only [map_mul, map_inv, hp', h1]
    group
  have hgcoe : (g : G) = (p' : G)⁻¹ * (t * l * t⁻¹) * (p' : G) * l⁻¹ := by
    rw [hgdef]
    simp [hconjT]
  have hact1 : ActCoord V β (g : G) 1 := by
    have h := hρ g
    rw [hgρ, Units.val_one] at h
    exact h
  have hEq : ((p' : G)⁻¹ * t) * l * ((p' : G)⁻¹ * t)⁻¹ * l⁻¹ = (g : G) := by
    rw [hgcoe]
    group
  rw [hEq]
  exact centralizer_of_actCoord_one_nsb31 hβi (hLV _ g.2) hact1

theorem T_acts_inner {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}
    (hd : NoSumBigData G T M L Mm I H K m k) :
    ∀ t ∈ T, ∃ p ∈ L, ∀ l ∈ L,
      (p⁻¹ * t) * l * (p⁻¹ * t)⁻¹ * l⁻¹ ∈ Subgroup.centralizer (vV T L : Set G) := by
  obtain ⟨-, -, c, hm34, hmk, -, -, hsum⟩ := hd
  obtain ⟨α, hα, -, hAV, -, β, hβs, hβk, hβe⟩ := hsum
  have hm : 0 < m := by
    rcases hm34 with h | h <;> omega
  have hk : 0 < k := by omega
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
    rw [← c.omega_eq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  have hLN : L ≤ Subgroup.normalizer (vV T L : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hTN' : T ≤ Subgroup.normalizer (vV T L : Set G) :=
    le_normalizer_commutator_nsb31 (le_sup_right.trans hRN) hTN
  have hLV : ∀ l ∈ L, ∀ x ∈ vV T L, l * x * l⁻¹ ∈ vV T L := fun l hl x hx =>
    (Subgroup.mem_normalizer_iff.mp (hLN hl) x).mp hx
  have hTV : ∀ t ∈ T, ∀ x ∈ vV T L, t * x * t⁻¹ ∈ vV T L := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTN' ht) x).mp hx
  have hTL : ∀ t ∈ T, ∀ x ∈ L, t * x * t⁻¹ ∈ L := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.mp (hTN ht) x).mp hx
  have hex : ∀ l ∈ L, ∃ X : Matrix.GeneralLinearGroup (Fin m) (ZMod 2),
      ActCoord (vV T L) β l (X : Matrix (Fin m) (Fin m) (ZMod 2)) := by
    intro l hl
    obtain ⟨a, ha, hact⟩ := c.exists_act_L hl
    have haA : a ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I := Subgroup.mem_sup_left ha
    refine ⟨((α ⟨a, haA⟩ : ↥(CFSG.Open.StatedSL m (ZMod 2))) :
      Matrix.GeneralLinearGroup (Fin m) (ZMod 2)), ?_⟩
    intro u v huv i
    have h := hβe ⟨a, haA⟩ u v (by rw [huv]; exact hact u u.2) i
    simpa [moduleAct] using h
  have hsurj : ∀ g : Matrix.GeneralLinearGroup (Fin m) (ZMod 2), ∃ l ∈ L,
      ActCoord (vV T L) β l (g : Matrix (Fin m) (Fin m) (ZMod 2)) := by
    intro g
    have hg : g ∈ CFSG.Open.StatedSL m (ZMod 2) := by
      rw [statedSL_zmod_two_eq_top]
      exact Subgroup.mem_top g
    obtain ⟨a, ha⟩ := hα ⟨g, hg⟩
    obtain ⟨a', ha', hact⟩ := c.exists_act_sup a.2
    refine ⟨a', ((perfectCore_le _).trans inf_le_left) ha', ?_⟩
    intro u v huv i
    have h := hβe a u v (by rw [huv]; exact (hact u u.2).symm) i
    have hαa : ((α a : ↥(CFSG.Open.StatedSL m (ZMod 2))) :
        Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) = g :=
      congrArg Subtype.val ha
    simpa [moduleAct, hαa] using h
  exact fun t ht => core_nsb31 hm hk hβs hβi hLV hTV hTL hex hsurj ht

end CFSG.Quasithin.H13.Ch4.NSB
