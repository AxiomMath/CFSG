module

import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartOne.EmbeddingTransport

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThreeEvenClassification.Helpers

theorem isKGroup_quotient {X : Type} [Group X] (hX : CFSG.IsKGroup X) (M : Subgroup X)
    [M.Normal] : CFSG.IsKGroup (X ⧸ M) :=
  hX.quotient M

theorem le_inSubgroup_perfectResidual_of_isPerfect {H : Type*} [Group H] [Finite H]
    {P X : Subgroup H} (hPX : P ≤ X) (hP : Group.IsPerfect P) :
    P ≤ inSubgroup perfectResidual X := by
  have hperf : Group.IsPerfect (P.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX).symm.surjective
  have h := (perfect_residual_transport (MonoidHom.id X)).2.2 (P.subgroupOf X) hperf
  exact fun x hx => ⟨⟨x, hPX hx⟩, h hx, rfl⟩

theorem map_mem_thetaComponents_of_surjective {G G' : Type*} [Group G] [Group G'] [Finite G]
    {p : ℕ} (hp : p.Prime) (f : G →* G') (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (hkp : ¬ p ∣ Nat.card f.ker) {Y : Subgroup G}
    (hY : Y ∈ thetaComponents p G) : Y.map f ∈ thetaComponents p G' := by
  have : Finite G' := Finite.of_surjective f hf
  set Z := Y.map f with hZ
  let g : Y →* Z := f.subgroupMap Y
  have hg : Function.Surjective g := f.subgroupMap_surjective Y
  have hgval : ∀ y : Y, ((g y : Z) : G') = f y := fun _ => rfl
  have hgker : ∀ y : Y, y ∈ g.ker ↔ (y : G) ∈ f.ker := fun y => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hgval y, OneMemClass.coe_eq_one]
  let ι : g.ker →* f.ker :=
    (Y.subtype.comp g.ker.subtype).codRestrict f.ker fun y => (hgker y.1).mp y.2
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => ((z : f.ker) : G)) h))
  have hKs : Group.IsSolvable g.ker := Group.isSolvable_of_isSolvable_injective hι
  have hKp : ¬ p ∣ Nat.card g.ker := fun h => hkp (h.trans (Subgroup.card_dvd_of_injective ι hι))
  obtain ⟨hKle, hθmap, -⟩ := solvable_prime_complement_core_quotient_centralizers hp g.ker hKs hKp
  let e : Y ⧸ g.ker ≃* Z := QuotientGroup.quotientKerEquivOfSurjective g hg
  have hθZ : aschbacherSolvableCore p Z = (aschbacherSolvableCore p Y).map g := by
    rw [← aschbacherSolvableCore_map_mulEquiv hp e, ← hθmap, Subgroup.map_map]
    rfl
  let ψ : Y →* Z ⧸ aschbacherSolvableCore p Z := (QuotientGroup.mk' _).comp g
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hg
  have hψker : ψ.ker = aschbacherSolvableCore p Y := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hθZ]
    constructor
    · rintro ⟨t, ht, hty⟩
      have h1 : t⁻¹ * y ∈ g.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hty, inv_mul_cancel]
      have h2 := Subgroup.mul_mem _ ht (hKle h1)
      rwa [mul_inv_cancel_left] at h2
    · intro hy
      exact ⟨y, hy, rfl⟩
  let e2 : Y ⧸ aschbacherSolvableCore p Y ≃* Z ⧸ aschbacherSolvableCore p Z :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  refine ⟨?_, hY.2.1.map hf, LocalCores.isQuasisimple_of_mulEquiv e2 hY.2.2⟩
  have := hY.1
  exact Group.IsPerfect.ofSurjective (f := g) hg

theorem exists_centralizer_surjection {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (hNp : ¬ p ∣ Nat.card N) {x : G}
    (hx : ∃ k : ℕ, orderOf x = p ^ k) :
    ∃ f : Subgroup.centralizer ({x} : Set G) →*
        Subgroup.centralizer ({QuotientGroup.mk' N x} : Set (G ⧸ N)),
      Function.Surjective f ∧
        (∀ c, ((f c : Subgroup.centralizer ({QuotientGroup.mk' N x} : Set (G ⧸ N))) : G ⧸ N) =
          QuotientGroup.mk' N (c : G)) ∧
        ¬ p ∣ Nat.card f.ker ∧ (Group.IsSolvable N → Group.IsSolvable f.ker) := by
  set π := QuotientGroup.mk' N
  have hpg : IsPGroup p (Subgroup.zpowers x) := by
    obtain ⟨k, hk⟩ := hx
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hmap : (Subgroup.centralizer ({x} : Set G)).map π =
      Subgroup.centralizer ({π x} : Set (G ⧸ N)) := by
    have h := centralizer_map_eq_of_pGroup_prime_complement_kernel p hp π
      (QuotientGroup.mk'_surjective N) (by rwa [QuotientGroup.ker_mk']) _ hpg
    rwa [← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, MonoidHom.map_zpowers,
      ← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at h
  let f : Subgroup.centralizer ({x} : Set G) →* Subgroup.centralizer ({π x} : Set (G ⧸ N)) :=
    (π.comp (Subgroup.centralizer ({x} : Set G)).subtype).codRestrict _
      fun c => hmap ▸ Subgroup.mem_map_of_mem π c.2
  have hf : Function.Surjective f := fun c' => by
    obtain ⟨c, hc, hcc⟩ := Subgroup.mem_map.mp
      (hmap.symm ▸ c'.2 : (c' : G ⧸ N) ∈ (Subgroup.centralizer ({x} : Set G)).map π)
    exact ⟨⟨c, hc⟩, Subtype.ext hcc⟩
  let ι : f.ker →* N :=
    ((Subgroup.centralizer ({x} : Set G)).subtype.comp f.ker.subtype).codRestrict N fun c =>
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val c.2)
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : G)) h))
  exact ⟨f, hf, fun _ => rfl, fun h => hNp (h.trans (Subgroup.card_dvd_of_injective ι hι)),
    fun h => Group.isSolvable_of_isSolvable_injective hι⟩

theorem map_mem_thetaComponentsAt_quotient {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (N : Subgroup G) [N.Normal] (hNs : Group.IsSolvable N)
    (hNp : ¬ p ∣ Nat.card N) {x : G} (hx : ∃ k : ℕ, orderOf x = p ^ k) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt p x) :
    Y.map (QuotientGroup.mk' N) ∈ thetaComponentsAt p (QuotientGroup.mk' N x) := by
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  obtain ⟨f, hf, hfπ, hkp, hks⟩ := exists_centralizer_surjection hp N hNp hx
  refine ⟨Y₀.map f, map_mem_thetaComponents_of_surjective hp f hf (hks hNs) hkp hY₀, ?_⟩
  have hcomp : (Subgroup.centralizer ({QuotientGroup.mk' N x} : Set (G ⧸ N))).subtype.comp f =
      (QuotientGroup.mk' N).comp (Subgroup.centralizer ({x} : Set G)).subtype :=
    MonoidHom.ext hfπ
  show (Y₀.map f).map _ = (Y₀.map _).map _
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

theorem mk_mem_normalizer_of_mem_normalizer_thetaComponents {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) {g : H}
    (hg : ∀ L ∈ thetaComponents p H, g ∈ Subgroup.normalizer (L : Set H))
    {J : Subgroup (H ⧸ aschbacherSolvableCore p H)} (hJ : IsComponent J) :
    QuotientGroup.mk' (aschbacherSolvableCore p H) g ∈
      Subgroup.normalizer (J : Set (H ⧸ aschbacherSolvableCore p H)) := by
  obtain ⟨hL, hLJ⟩ := perfectResidual_comap_mem_thetaComponents hp hJ
  have h := (mem_normalizer_iff_mk_mem_normalizer hp hL g).mp (hg _ hL)
  rwa [hLJ] at h

end CFSG.RankThree.PartOne.EmbeddingTransport
