module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92SylMat
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92SylStab
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92SylWeak

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}

omit [Finite G] in
private theorem conjMatHom_range_eq_xg {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E) :
    (conjMatHom hB).range = (ggAutomizer ⊤ B.span).map B.glHom := by
  rw [conjMatHom, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (normalizerToBspan_surjective hB), Subgroup.map_top,
    normalizerMonoidHom_range_eq_ggAutomizer]

private theorem card_eq_card_inf_mul_card_map {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    {F : Subgroup G} (hFN : F ≤ Subgroup.normalizer (E : Set G)) :
    Nat.card F = Nat.card ↥(F ⊓ Subgroup.centralizer (E : Set G)) *
      Nat.card ↥((F.subgroupOf (Subgroup.normalizer (E : Set G))).map (conjMatHom hB)) := by
  let f : ↥F →* GL (Fin 6) (ZMod 3) := (conjMatHom hB).comp (Subgroup.inclusion hFN)
  have hker : f.ker = (F ⊓ Subgroup.centralizer (E : Set G)).subgroupOf F := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, conjMatHom_ker hB]
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  have hrange : f.range =
      (F.subgroupOf (Subgroup.normalizer (E : Set G))).map (conjMatHom hB) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hidx : (F ⊓ Subgroup.centralizer (E : Set G)).relIndex F = Nat.card f.range := by
    rw [← Subgroup.index_ker f, hker]
    rfl
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) F
  rw [← Subgroup.inf_relIndex_left F, hidx, hrange,
    inf_comm (Subgroup.centralizer (E : Set G)) F] at h1
  rw [← h1, mul_comm]

omit [Finite G] in
private theorem conjMatHom_mulVec_e_two {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (x : ↥(Subgroup.normalizer (E : Set G)))
    (hx : (x : G) ∈ Subgroup.centralizer ({B.b 2} : Set G)) :
    ((conjMatHom hB x : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      Pi.single 2 1 = Pi.single 2 1 := by
  have hxb : (x : G) * B.b 2 * (x : G)⁻¹ = B.b 2 := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  have hxS : (x : G) ∈ Subgroup.normalizer (B.span : Set G) := by
    rw [hB.1]
    exact x.2
  have hacts : B.Acts (x : G) ((conjMatHom hB x : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
    rw [conjMatHom_apply]
    exact B.acts_matOf (fun y =>
      Subgroup.normalizerMonoidHom_apply_apply_coe B.span (normalizerToBspan hB x) y)
  have h1 := B.acts_vec' hxS hacts (Pi.single 2 1)
  rw [B.vec_single, hxb] at h1
  apply B.vec_injective
  rw [← h1, B.vec_single]

theorem card_le_of_isPGroup_le_centralizer_b_two
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀) {P : Subgroup G}
    (hP : IsPGroup 3 P) (hPC : P ≤ Subgroup.centralizer ({B.b 2} : Set G)) :
    Nat.card P ≤ 3 ^ 8 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd' : StdTwD5 b₀ K E := hstd
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -, hEmax, -, -, -⟩ := hhyp
  obtain ⟨-, hsup, -, hEKcard, hCK⟩ := hcanon
  have hOut : ¬ 3 ∣ Nat.card (Outer K) := not_three_dvd_card_outer_of_isTwD5 hKmark hKz
  have hX := glHom_ggAutomizer_eq_oE6_one hstd' hB hrec hfus
  have hcardX : Nat.card ↥(oE6 1) = 103680 := by
    rw [← hX, Subgroup.card_map_of_injective B.glHom_injective]
    exact hrec.1
  have hnorm : ¬ (Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
    have h := hfus.1
    rwa [hB.1] at h
  set C₂ := Subgroup.centralizer ({B.b 2} : Set G) with hC₂
  have hb2E : B.b 2 ∈ E := by
    rw [← hB.1]
    exact B.b_mem_span 2
  have hEC₂ : E ≤ C₂ := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hEmax.2.1.comm he hb2E)
  have hEp : IsPGroup 3 (E.subgroupOf C₂) := fun x => by
    obtain ⟨k, hk⟩ := hEmax.2.1.isPGroup ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  set S₂ : Subgroup G := (S : Subgroup C₂).map C₂.subtype with hS₂
  have hS₂p : IsPGroup 3 S₂ := S.isPGroup'.map _
  have hS₂C : S₂ ≤ C₂ := Subgroup.map_subtype_le _
  have hES₂ : E ≤ S₂ := fun x hx =>
    ⟨⟨x, hEC₂ hx⟩, hES (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hPle : Nat.card P ≤ Nat.card S₂ := by
    rw [Subgroup.card_map_of_injective C₂.subtype_injective, Sylow.card_eq_multiplicity]
    exact fs81Nt_card_le_of_isPGroup hP hPC
  have hS₂N : S₂ ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_of_isPGroup_of_oE6 hstd' hB hfus hX
      (fun A hA h3 => mem_wE6_of_mem_oE6_of_pow_three hA h3) hS₂p hES₂
  have hS₂E : S₂ ⊓ Subgroup.centralizer (E : Set G) ≤ E := by
    intro y hy
    obtain ⟨k, hk⟩ := hS₂p ⟨y, hy.1⟩
    exact fs81_three_elem_mem_E hb₀ hKC hKn hOut hA2 hsup hCK hEmax.2.1 hnorm hy.2
      (k := k) (by simpa using congrArg Subtype.val hk)
  have hEcard : Nat.card E = 3 ^ 6 := by
    rw [card_E_eq_three_mul_card_inf_of_std hstd', hEKcard]
    norm_num
  have hcent : Nat.card ↥(S₂ ⊓ Subgroup.centralizer (E : Set G)) ≤ 3 ^ 6 :=
    hEcard ▸ Subgroup.card_le_of_le hS₂E
  set N := Subgroup.normalizer (E : Set G) with hN
  have hS₂p' : IsPGroup 3 (S₂.subgroupOf N) := fun x => by
    obtain ⟨k, hk⟩ := hS₂p ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hbar : Nat.card ↥((S₂.subgroupOf N).map (conjMatHom hB)) ≤ 9 := by
    refine card_le_nine_of_isPGroup_of_mulVec_e_two hcardX (hS₂p'.map _) ?_ ?_
    · rintro _ ⟨x, -, rfl⟩
      rw [← hX, ← conjMatHom_range_eq_xg hB]
      exact ⟨x, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact conjMatHom_mulVec_e_two hB x (hS₂C (Subgroup.mem_subgroupOf.mp hx))
  calc Nat.card P ≤ Nat.card S₂ := hPle
    _ = Nat.card ↥(S₂ ⊓ Subgroup.centralizer (E : Set G)) *
          Nat.card ↥((S₂.subgroupOf N).map (conjMatHom hB)) :=
        card_eq_card_inf_mul_card_map hB hS₂N
    _ ≤ 3 ^ 6 * 9 := Nat.mul_le_mul hcent hbar
    _ = 3 ^ 8 := by norm_num

theorem not_three_pow_nine_dvd_card_of_le_centralizer_b_two
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({B.b 2} : Set G)) : ¬ 3 ^ 9 ∣ Nat.card L := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 h
  have hcard : Nat.card ↥(H.map L.subtype) = 3 ^ 9 :=
    (Subgroup.card_map_of_injective L.subtype_injective).trans hH
  have hle := card_le_of_isPGroup_le_centralizer_b_two hstd hB hrec hfus (IsPGroup.of_card hcard)
    ((Subgroup.map_subtype_le H).trans hL)
  rw [hcard] at hle
  norm_num at hle

theorem not_three_pow_nine_dvd_card_of_surjective
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({B.b 2} : Set G)) {Q : Type*} [Group Q] (π : ↥L →* Q)
    (hπ : Function.Surjective π) : ¬ 3 ^ 9 ∣ Nat.card Q := by
  intro h9
  have hLQ : Nat.card L = Nat.card π.ker * Nat.card Q := by
    have h1 := Subgroup.card_mul_index π.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top] at h1
    exact h1.symm
  exact not_three_pow_nine_dvd_card_of_le_centralizer_b_two hstd hB hrec hfus hL
    (h9.trans (hLQ ▸ Dvd.intro_left _ rfl))

theorem card_le_of_isPGroup_of_surjective
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({B.b 2} : Set G)) {Q : Type*} [Group Q] (π : ↥L →* Q)
    (hπ : Function.Surjective π) {P : Subgroup Q} (hP : IsPGroup 3 P) :
    Nat.card P ≤ 3 ^ 8 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Finite.of_surjective π hπ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  refine Nat.pow_le_pow_right (by norm_num) (not_lt.mp fun h9 => ?_)
  have hkQ : 3 ^ k ∣ Nat.card Q := by
    rw [← hk]
    exact Subgroup.card_subgroup_dvd_card P
  exact not_three_pow_nine_dvd_card_of_surjective hstd hB hrec hfus hL π hπ
    ((pow_dvd_pow 3 (show 9 ≤ k by omega)).trans hkQ)

end CFSG.StandardType.FrameRoute.FS81

end
