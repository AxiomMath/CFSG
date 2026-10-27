module

public import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def imageSub (K D : Subgroup G) :
    Subgroup (K ⧸ aschbacherSolvableCore 3 K) :=
  (D.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))

theorem mem_normalizer_inf' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨(hA y).mp ha, (hB y).mp hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(hA y).mpr ha, (hB y).mpr hb⟩

theorem ker_le_ker_of_theta_bot {D P Lb : Type*} [Group D] [Group P] [Group Lb] [Finite P]
    (f : D →* P) (hf : Function.Surjective f) (g : D →* Lb) (hs : Group.IsSolvable g.ker)
    (h3 : ¬ 3 ∣ Nat.card g.ker) (hθ : aschbacherSolvableCore 3 P = ⊥) : g.ker ≤ f.ker := by
  have hQn : (g.ker.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hQs : Group.IsSolvable (g.ker.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective g.ker)
  have hQ3 : ¬ 3 ∣ Nat.card (g.ker.map f) := fun h =>
    h3 (h.trans (Subgroup.card_map_dvd g.ker f))
  have hmaxP : ∀ N : Subgroup P, N.Normal → Group.IsSolvable N → ¬ 3 ∣ Nat.card N →
      N ≤ aschbacherSolvableCore 3 P :=
    (solvable_prime_complement_core_characterization (H := P) Nat.prime_three).2.2.2.1
  have hQle := hmaxP _ hQn hQs hQ3
  rw [hθ] at hQle
  intro z hz
  have h2 := hQle (Subgroup.mem_map_of_mem f hz)
  rw [Subgroup.mem_bot] at h2
  exact h2

theorem exists_embedding {L K : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥)
    (hDK : Sec11.sec11K L d ≤ K)
    (hθP : aschbacherSolvableCore 3 (imageSub K (Sec11.sec11K L d)) = ⊥) :
    ∃ ψ : imageSub K (Sec11.sec11K L d) →* L ⧸ aschbacherSolvableCore 3 L,
      Function.Injective ψ ∧
      ∀ (z : Sec11.sec11K L d) (p : imageSub K (Sec11.sec11K L d)),
        (p : K ⧸ aschbacherSolvableCore 3 K) =
          QuotientGroup.mk' (aschbacherSolvableCore 3 K) (Subgroup.inclusion hDK z) →
        ψ p = Sec11.kMap L d z := by
  classical
  set D := Sec11.sec11K L d with hD
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  set P := imageSub K D with hP
  let fD : D →* K ⧸ aschbacherSolvableCore 3 K := π.comp (Subgroup.inclusion hDK)
  have hfD : ∀ z, fD z ∈ P := fun z =>
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr z.2)
  let f : D →* P := fD.codRestrict P hfD
  have hf : Function.Surjective f := by
    rintro ⟨p, y, hy, rfl⟩
    exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext rfl⟩
  set g := Sec11.kMap L d with hg
  obtain ⟨hθs, -, hθ3, hmax, -⟩ := solvable_prime_complement_core_characterization (H := D)
    Nat.prime_three
  obtain ⟨hθLs, -, hθL3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  obtain ⟨hθKs, hθK3⟩ := Sec6.theta_solvable_and_not_dvd K
  have hker1 : f.ker ≤ g.ker := by
    intro z hz
    have h1 : fD z = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    have h2 : Subgroup.inclusion hDK z ∈ aschbacherSolvableCore 3 K := by
      have : π (Subgroup.inclusion hDK z) = 1 := h1
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hzθ : (z : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := ⟨_, h2, rfl⟩
    set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
    set N := D ⊓ θK with hN
    have hND : N ≤ D := inf_le_left
    have hDN : D ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
      mem_normalizer_inf' (Subgroup.le_normalizer hx) (Sec6.le_normalizer_theta K (hDK hx))
    have hNs : Group.IsSolvable N :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
        (inf_le_right : N ≤ θK))
    have hN3 : ¬ 3 ∣ Nat.card N := fun h => hθK3 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
    have hle := Sec6.le_theta_of_normal hND hDN hNs hN3 ⟨z.2, hzθ⟩
    obtain ⟨y, hy, hyz⟩ := hle
    have hyz' : y = z := Subtype.ext hyz
    rw [hyz'] at hy
    exact Sec11.le_ker_kMap_of_normal_solvable hdN hd3 hQ hZ (aschbacherSolvableCore 3 D) hθs hy
  have hker2 : g.ker ≤ f.ker := by
    set N' := g.ker with hN'
    have hkker : ∀ k : N',
        Subgroup.inclusion (Sec11.sec11K_le L d) (k : D) ∈ aschbacherSolvableCore 3 L :=
      fun k => by
        have h1 : g (k : D) = 1 := MonoidHom.mem_ker.mp k.2
        change QuotientGroup.mk' (aschbacherSolvableCore 3 L)
          (Subgroup.inclusion (Sec11.sec11K_le L d) (k : D)) = 1 at h1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
    set fι : N' →* aschbacherSolvableCore 3 L :=
      ((Subgroup.inclusion (Sec11.sec11K_le L d)).comp N'.subtype).codRestrict _ hkker with hfι
    have hfιinj : Function.Injective fι := fun y z hyz => Subtype.ext (Subtype.ext (by
      have := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) hyz
      exact this))
    have hN's : Group.IsSolvable N' := Group.isSolvable_of_isSolvable_injective hfιinj
    have hN'3 : ¬ 3 ∣ Nat.card N' := fun h =>
      hθL3 (h.trans (Subgroup.card_dvd_of_injective fι hfιinj))
    exact ker_le_ker_of_theta_bot f hf g hN's hN'3 hθP
  have hker : f.ker = g.ker := le_antisymm hker1 hker2
  let ψ : P →* L ⧸ aschbacherSolvableCore 3 L :=
    f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf) ⟨g, hker1⟩
  have hψ : ∀ z, ψ (f z) = g z := fun z =>
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨g, hker1⟩ z
  refine ⟨ψ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro p hp
    obtain ⟨z, rfl⟩ := hf p
    rw [hψ] at hp
    have : z ∈ g.ker := MonoidHom.mem_ker.mpr hp
    have h2 : z ∈ f.ker := hker2 this
    exact MonoidHom.mem_ker.mp h2
  · intro z p hp
    have : p = f z := Subtype.ext hp
    rw [this, hψ]

theorem kMap_conj_apply {L : Subgroup G} {d s : G} (hsL : s ∈ Subgroup.normalizer (L : Set G))
    (z z' : Sec11.sec11K L d) (hz' : (z' : G) = s * z * s⁻¹) :
    Sec11.kMap L d z' = Sec4.Item426.thetaAut L hsL (Sec11.kMap L d z) := by
  change QuotientGroup.mk' (aschbacherSolvableCore 3 L)
      (Subgroup.inclusion (Sec11.sec11K_le L d) z') =
    Sec4.Item426.thetaAut L hsL (QuotientGroup.mk' (aschbacherSolvableCore 3 L)
      (Subgroup.inclusion (Sec11.sec11K_le L d) z))
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  rw [Sec4.Item426.thetaAut_mk]
  congr 1
  apply Subtype.ext
  rw [Sec4.Item426.coe_compAction_apply]
  exact hz'

theorem mk_inclusion_conj {K D : Subgroup G} {s : G} (hsK : s ∈ K) (hDK : D ≤ K) (z z' : D)
    (hz' : (z' : G) = s * z * s⁻¹) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 K) (Subgroup.inclusion hDK z') =
      QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨s, hsK⟩ *
        QuotientGroup.mk' (aschbacherSolvableCore 3 K) (Subgroup.inclusion hDK z) *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨s, hsK⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact hz'

end CFSG.RankThree.PartTwo.Sec8.Hering611
