module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem exists_secMod_embedding {G : Type} [Group G] {R V P W : Subgroup G}
    {U Y : Type} [AddCommGroup U] [DistribMulAction ↥R U] [AddCommGroup Y]
    [DistribMulAction ↥R Y] {κU : ↥W →* Multiplicative U} {κY : ↥P →* Multiplicative Y}
    (hU : IsSecMod R W V U κU) (hY : IsSecMod R P V Y κY) (hVP : V ≤ P) (hPW : P ≤ W)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) :
    ∃ ι : Y →+ U, Function.Injective ι ∧ (∀ (r : ↥R) (y : Y), ι (r • y) = r • ι y) ∧
      (∀ p : ↥P, ι (Multiplicative.toAdd (κY p)) =
        Multiplicative.toAdd (κU ⟨(p : G), hPW p.2⟩)) ∧ ι.range = secSub κU P := by
  let κ' : ↥P →* Multiplicative U := κU.comp (Subgroup.inclusion hPW)
  have hker : κY.ker ≤ κ'.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (hU.ker (Subgroup.inclusion hPW x)).mpr ((hY.ker x).mp hx)
  let φ : Multiplicative Y →* Multiplicative U :=
    κY.liftOfRightInverse (Function.surjInv hY.surj) (Function.rightInverse_surjInv hY.surj)
      ⟨κ', hker⟩
  have hφ : ∀ p : ↥P, φ (κY p) = κU ⟨(p : G), hPW p.2⟩ := fun p =>
    MonoidHom.liftOfRightInverse_comp_apply κY _ _ ⟨κ', hker⟩ p
  let ι : Y →+ U :=
    { toFun := fun y => Multiplicative.toAdd (φ (Multiplicative.ofAdd y))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add, toAdd_mul] }
  have hι : ∀ p : ↥P, ι (Multiplicative.toAdd (κY p)) =
      Multiplicative.toAdd (κU ⟨(p : G), hPW p.2⟩) := fun p => by
    show Multiplicative.toAdd (φ (Multiplicative.ofAdd (Multiplicative.toAdd (κY p)))) = _
    rw [ofAdd_toAdd, hφ]
  refine ⟨ι, ?_, ?_, hι, ?_⟩
  · refine (injective_iff_map_eq_zero ι).mpr fun y hy => ?_
    obtain ⟨p, hp⟩ := hY.surj (Multiplicative.ofAdd y)
    have hy' : Multiplicative.toAdd (κY p) = y := by rw [hp, toAdd_ofAdd]
    have h1 : Multiplicative.toAdd (κU ⟨(p : G), hPW p.2⟩) = 0 := by
      rw [← hι p, hy']
      exact hy
    have h2 : κY p = 1 := (hY.ker p).mpr ((hU.ker _).mp (toAdd_eq_zero.mp h1))
    rw [hp] at h2
    exact ofAdd_eq_one.mp h2
  · intro r y
    obtain ⟨p, hp⟩ := hY.surj (Multiplicative.ofAdd y)
    have hy' : Multiplicative.toAdd (κY p) = y := by rw [hp, toAdd_ofAdd]
    obtain ⟨q, hq⟩ : ∃ q : ↥P, (q : G) = (r : G) * (p : G) * (r : G)⁻¹ :=
      ⟨⟨(r : G) * (p : G) * (r : G)⁻¹, hP r r.2 p p.2⟩, rfl⟩
    have h1 : r • Multiplicative.toAdd (κY p) = Multiplicative.toAdd (κY q) := by
      rw [hY.act r p q hq, toAdd_ofAdd]
    have h2 : r • Multiplicative.toAdd (κU ⟨(p : G), hPW p.2⟩) =
        Multiplicative.toAdd (κU ⟨(q : G), hPW q.2⟩) := by
      rw [hU.act r ⟨(p : G), hPW p.2⟩ ⟨(q : G), hPW q.2⟩ hq, toAdd_ofAdd]
    rw [← hy', h1, hι, hι, h2]
  · ext a
    rw [AddMonoidHom.mem_range, mem_secSub]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨p, hp⟩ := hY.surj (Multiplicative.ofAdd y)
      have hy' : Multiplicative.toAdd (κY p) = y := by rw [hp, toAdd_ofAdd]
      refine ⟨⟨(p : G), hPW p.2⟩, p.2, ?_⟩
      rw [← hy', hι p, ofAdd_toAdd]
    · rintro ⟨x, hxP, hx⟩
      refine ⟨Multiplicative.toAdd (κY ⟨(x : G), hxP⟩), ?_⟩
      rw [hι ⟨(x : G), hxP⟩]
      show Multiplicative.toAdd (κU x) = a
      rw [hx, toAdd_ofAdd]

theorem isSecMod_restrict {G : Type} [Group G] {R R' P I : Subgroup G} {Y : Type}
    [AddCommGroup Y] [DistribMulAction ↥R' Y] {κ : ↥P →* Multiplicative Y} (hRR : R ≤ R')
    (h : IsSecMod R' P I Y κ) :
    @IsSecMod G _ R P I Y _ (DistribMulAction.compHom Y (Subgroup.inclusion hRR)) κ := by
  refine @IsSecMod.mk G _ R P I Y _ (DistribMulAction.compHom Y (Subgroup.inclusion hRR)) κ
    h.surj h.ker (fun r x y hxy => h.act (Subgroup.inclusion hRR r) x y hxy) h.two

end CFSG.RankThree.GF2n.Stroth80
