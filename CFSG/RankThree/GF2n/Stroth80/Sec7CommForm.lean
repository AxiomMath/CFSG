module

public import CFSG.RankThree.GF2n.Stroth80.Sec711Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Matrix MatrixGroups commutatorElement

theorem lamOrth_radical_le {G : Type} [Group G] [Finite G] {Q Z V W : Subgroup G}
    (lam : ↥Z →* Multiplicative (ZMod 2))
    (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ a ∈ Q, Commute z a)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z) (hsq : ∀ a ∈ Q, a ^ 2 ∈ Z)
    (hnd : ∀ a ∈ Q, (∀ b ∈ Q, LamOrth Z lam a b) → a ∈ Z)
    (hZV : Z ≤ V) (hVW : V ≤ W) (hWQ : W ≤ Q)
    (hW : ∀ a ∈ Q, a ∈ W ↔ ∀ v ∈ V, LamOrth Z lam a v) :
    ∀ a ∈ W, (∀ w ∈ W, LamOrth Z lam a w) → a ∈ V := by
  classical
  have hVQ : V ≤ Q := hVW.trans hWQ
  have hZW : Z ≤ W := hZV.trans hVW
  have hsec : SecHyp (⊥ : Subgroup G) Q Z :=
    ⟨hZQ, hcomm, hsq, fun r hr x hx => by simpa [Subgroup.mem_bot.mp hr] using hx,
      fun r hr x hx => by simpa [Subgroup.mem_bot.mp hr] using hx⟩
  obtain ⟨M, iM, iA, κ, hκ⟩ := exists_sectionModule hsec
  haveI : Finite M := hκ.finite
  letI : Module (ZMod 2) M := AddCommGroup.zmodModule (fun a => by
    rw [two_nsmul]; exact hκ.two a)
  haveI : FiniteDimensional (ZMod 2) M := Module.Finite.of_finite
  obtain ⟨f, hfnd, hfalt, hfκ⟩ := exists_lamForm lam hcomm hZc hκ hnd
  let Sub : Subgroup G → Submodule (ZMod 2) M := fun U =>
    AddSubgroup.toZModSubmodule 2 (secSub κ U)
  have hrep : ∀ x : M, ∃ a : ↥Q, Multiplicative.toAdd (κ a) = x := by
    intro x
    obtain ⟨a, ha⟩ := hκ.surj (Multiplicative.ofAdd x)
    exact ⟨a, by rw [ha]; rfl⟩
  have hmemU : ∀ U : Subgroup G, Z ≤ U → ∀ a : ↥Q,
      Multiplicative.toAdd (κ a) ∈ Sub U ↔ (a : G) ∈ U :=
    fun U hU a => toAdd_mem_secSub_iff hκ hU a
  have horth : f.orthogonal (Sub V) = Sub W := by
    ext x
    obtain ⟨a, rfl⟩ := hrep x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    have h1 : (∀ n ∈ Sub V, f n (Multiplicative.toAdd (κ a)) = 0) ↔
        ∀ v : ↥Q, (v : G) ∈ V → comm2 lam hcomm v a = 0 := by
      constructor
      · intro h v hv
        rw [← hfκ]
        exact h _ ((hmemU V hZV v).2 hv)
      · intro h n hn
        obtain ⟨v, rfl⟩ := hrep n
        rw [hfκ]
        exact h v ((hmemU V hZV v).1 hn)
    refine (h1.trans ?_).trans (hmemU W hZW a).symm
    rw [hW a a.2]
    constructor
    · intro h v hv
      have := h ⟨v, hVQ hv⟩ hv
      rw [comm2_symm lam hcomm hZc, comm2_eq_zero_iff lam hcomm] at this
      exact this
    · intro h v hv
      rw [comm2_symm lam hcomm hZc, comm2_eq_zero_iff lam hcomm]
      exact h v hv
  have hdouble : f.orthogonal (Sub W) = Sub V := by
    rw [← horth, LinearMap.BilinForm.orthogonal_orthogonal hfnd
      (LinearMap.BilinForm.IsAlt.isRefl hfalt)]
  intro a ha hrad
  have haQ : a ∈ Q := hWQ ha
  have hκa : Multiplicative.toAdd (κ ⟨a, haQ⟩) ∈ f.orthogonal (Sub W) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨s, rfl⟩ := hrep n
    have hs : (s : G) ∈ W := (hmemU W hZW s).1 hn
    rw [hfκ, comm2_symm lam hcomm hZc, comm2_eq_zero_iff lam hcomm]
    exact hrad s hs
  rw [hdouble] at hκa
  exact (hmemU V hZV ⟨a, haQ⟩).1 hκa

theorem exists_commForm_WV {G : Type} [Group G] {Q Z V W R : Subgroup G}
    (lam : ↥Z →* Multiplicative (ZMod 2))
    (hZQ : Z ≤ Q) (hZc : ∀ z ∈ Z, ∀ a ∈ Q, Commute z a)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z)
    (hZV : Z ≤ V) (hVW : V ≤ W) (hWQ : W ≤ Q)
    (hVW1 : ∀ v ∈ V, ∀ w ∈ W, ⁅v, w⁆ = 1)
    {Y : Type} [AddCommGroup Y] [DistribMulAction ↥R Y] {κ : ↥W →* Multiplicative Y}
    (hκ : IsSecMod R W V Y κ) (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ = z)
    (hRW : ∀ r ∈ R, ∀ x ∈ W, r * x * r⁻¹ ∈ W)
    (hrad : ∀ a ∈ W, (∀ w ∈ W, LamOrth Z lam a w) → a ∈ V) :
    ∃ β : Y →+ Y →+ ZMod 2, (∀ (r : ↥R) (a b : Y), β (r • a) (r • b) = β a b) ∧
      ∀ a : Y, (∀ b : Y, β a b = 0) → a = 0 := by
  classical
  have hs : ∀ x : Y, ∃ a : ↥W, κ a = Multiplicative.ofAdd x := fun x => hκ.surj _
  choose lft hlft using hs
  obtain ⟨c2, hc2⟩ : ∃ c2 : ↥W → ↥W → ZMod 2, ∀ a b : ↥W,
      c2 a b = comm2 lam hcomm ⟨(a : G), hWQ a.2⟩ ⟨(b : G), hWQ b.2⟩ :=
    ⟨fun a b => comm2 lam hcomm ⟨(a : G), hWQ a.2⟩ ⟨(b : G), hWQ b.2⟩, fun a b => rfl⟩
  have comm2_of_eq : ∀ (p q p' q' : ↥Q), ⁅(p : G), (q : G)⁆ = ⁅(p' : G), (q' : G)⁆ →
      comm2 lam hcomm p q = comm2 lam hcomm p' q' := by
    intro p q p' q' h
    unfold comm2
    have e : (⟨⁅(p : G), (q : G)⁆, hcomm _ p.2 _ q.2⟩ : ↥Z) =
        ⟨⁅(p' : G), (q' : G)⁆, hcomm _ p'.2 _ q'.2⟩ := Subtype.ext h
    rw [e]
  have c2V : ∀ v b : ↥W, (v : G) ∈ V → c2 v b = 0 := by
    intro v b hv
    rw [hc2]
    unfold comm2
    have e : (⟨⁅(v : G), (b : G)⁆, hcomm _ (hWQ v.2) _ (hWQ b.2)⟩ : ↥Z) = 1 :=
      Subtype.ext (hVW1 _ hv _ b.2)
    rw [e, map_one, toAdd_one]
  have c2ML : ∀ a a' b : ↥W, c2 (a * a') b = c2 a b + c2 a' b := by
    intro a a' b
    rw [hc2, hc2, hc2]
    exact comm2_mul_left lam hcomm hZc ⟨(a : G), hWQ a.2⟩ ⟨(a' : G), hWQ a'.2⟩
      ⟨(b : G), hWQ b.2⟩
  have c2_symm : ∀ a b : ↥W, c2 a b = c2 b a := by
    intro a b
    rw [hc2, hc2]
    exact (comm2_symm lam hcomm hZc _ _).symm
  have c2L : ∀ a a' b : ↥W, (a : G) * (a' : G)⁻¹ ∈ V → c2 a b = c2 a' b := by
    intro a a' b h
    have hsplit : c2 a b = c2 (a * a'⁻¹ * a') b := by rw [inv_mul_cancel_right]
    rw [hsplit, c2ML, c2V (a * a'⁻¹) b h, zero_add]
  have c2R : ∀ a b b' : ↥W, (b : G) * (b' : G)⁻¹ ∈ V → c2 a b = c2 a b' := by
    intro a b b' h
    rw [c2_symm a b, c2_symm a b']
    exact c2L b b' a h
  have c2MR : ∀ a b b' : ↥W, c2 a (b * b') = c2 a b + c2 a b' := by
    intro a b b'
    rw [c2_symm a (b * b'), c2ML, c2_symm b a, c2_symm b' a]
  have liftmul : ∀ x x' : Y,
      ((lft (x + x') : ↥W) : G) * ((lft x * lft x' : ↥W) : G)⁻¹ ∈ V := by
    intro x x'
    apply (hκ.eq_iff _ _).1
    rw [hlft, map_mul, hlft, hlft, ofAdd_add]
  obtain ⟨F, hF⟩ : ∃ F : Y → Y → ZMod 2, ∀ x y, F x y = c2 (lft x) (lft y) :=
    ⟨fun x y => c2 (lft x) (lft y), fun x y => rfl⟩
  have keyF : ∀ (a b : ↥W) (x y : Y), κ a = Multiplicative.ofAdd x →
      κ b = Multiplicative.ofAdd y → c2 a b = F x y := by
    intro a b x y ha hb
    rw [hF]
    have h1 : κ a = κ (lft x) := ha.trans (hlft x).symm
    have h2 : κ b = κ (lft y) := hb.trans (hlft y).symm
    rw [c2L a (lft x) b ((hκ.eq_iff a (lft x)).1 h1),
      c2R (lft x) b (lft y) ((hκ.eq_iff b (lft y)).1 h2)]
  have hadd1 : ∀ x x' y, F (x + x') y = F x y + F x' y := by
    intro x x' y
    rw [hF, hF, hF, c2L _ _ _ (liftmul x x'), c2ML]
  have hadd2 : ∀ x y y', F x (y + y') = F x y + F x y' := by
    intro x y y'
    rw [hF, hF, hF, c2R _ _ _ (liftmul y y'), c2MR]
  have c2conj : ∀ (r : ↥R) (a b : ↥W),
      c2 ⟨(r : G) * (a : G) * (r : G)⁻¹, hRW r r.2 _ a.2⟩
        ⟨(r : G) * (b : G) * (r : G)⁻¹, hRW r r.2 _ b.2⟩ = c2 a b := by
    intro r a b
    rw [hc2, hc2]
    apply comm2_of_eq
    show ⁅(r : G) * (a : G) * (r : G)⁻¹, (r : G) * (b : G) * (r : G)⁻¹⁆ =
      ⁅(a : G), (b : G)⁆
    have h1 := hRZ r r.2 ⁅(a : G), (b : G)⁆ (hcomm _ (hWQ a.2) _ (hWQ b.2))
    have e' : ⁅(r : G) * (a : G) * (r : G)⁻¹, (r : G) * (b : G) * (r : G)⁻¹⁆ =
        (r : G) * ⁅(a : G), (b : G)⁆ * (r : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    exact e'.trans h1
  have hinv : ∀ (r : ↥R) (x y : Y), F (r • x) (r • y) = F x y := by
    intro r x y
    have hA := hκ.act r (lft x) ⟨(r : G) * (lft x : G) * (r : G)⁻¹, hRW r r.2 _ (lft x).2⟩ rfl
    have hB := hκ.act r (lft y) ⟨(r : G) * (lft y : G) * (r : G)⁻¹, hRW r r.2 _ (lft y).2⟩ rfl
    rw [hlft, toAdd_ofAdd] at hA hB
    rw [← keyF _ _ (r • x) (r • y) hA hB, ← keyF (lft x) (lft y) x y (hlft x) (hlft y)]
    exact c2conj r (lft x) (lft y)
  have hnd' : ∀ x : Y, (∀ y : Y, F x y = 0) → x = 0 := by
    intro x hx
    have hall : ∀ w ∈ W, LamOrth Z lam ((lft x : ↥W) : G) w := by
      intro w hw
      have h1 : c2 (lft x) ⟨w, hw⟩ = 0 := by
        rw [keyF (lft x) ⟨w, hw⟩ x (Multiplicative.toAdd (κ ⟨w, hw⟩)) (hlft x)
          (ofAdd_toAdd _).symm]
        exact hx _
      rw [hc2] at h1
      exact (comm2_eq_zero_iff lam hcomm _ _).1 h1
    have hV : ((lft x : ↥W) : G) ∈ V := hrad _ (lft x).2 hall
    have h2 : κ (lft x) = 1 := (hκ.ker _).2 hV
    rw [hlft] at h2
    exact ofAdd_eq_one.mp h2
  have hzero1 : ∀ y, F 0 y = 0 := fun y => by simpa using hadd1 0 0 y
  have hzero2 : ∀ x, F x 0 = 0 := fun x => by simpa using hadd2 x 0 0
  obtain ⟨Fh, hFh⟩ : ∃ Fh : Y → Y →+ ZMod 2, ∀ x y, Fh x y = F x y :=
    ⟨fun x => { toFun := F x, map_zero' := hzero2 x, map_add' := hadd2 x }, fun x y => rfl⟩
  have hFh0 : Fh 0 = 0 := AddMonoidHom.ext fun y => by
    rw [hFh, AddMonoidHom.zero_apply]
    exact hzero1 y
  have hFhadd : ∀ x x' : Y, Fh (x + x') = Fh x + Fh x' := fun x x' =>
    AddMonoidHom.ext fun y => by
      rw [AddMonoidHom.add_apply, hFh, hFh, hFh]
      exact hadd1 x x' y
  refine ⟨{ toFun := Fh, map_zero' := hFh0, map_add' := hFhadd }, fun r a b => ?_,
    fun x hx => hnd' x (fun y => (hFh x y).symm.trans (hx y))⟩
  exact (hFh _ _).trans ((hinv r a b).trans (hFh a b).symm)

end CFSG.RankThree.GF2n.Stroth80
