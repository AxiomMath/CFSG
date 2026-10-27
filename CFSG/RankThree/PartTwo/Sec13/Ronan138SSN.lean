module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKM12
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item138ProofSylow
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Ronan138SRefl
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SEnd
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKPGL

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step138KStr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → ∀ F : Subgroup G, IsF138N L E F →
      ∃ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E ∧ K ∈ lA E e ∧ e ∈ F ∧
        e ∉ Subgroup.zpowers c ∧ e ∉ L ∧
        (Sec8.IsZ3PGLThreePi (lBarA e K E) ∨
          Nonempty (lBarA e K E ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12))

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open scoped commutatorElement

section Prod

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_mul_pow_of_card {Z : Subgroup G} {a b : G} (haZ : a ∈ Z) (hbZ : b ∈ Z)
    (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) (hZ9 : Nat.card Z = 9) {z : G}
    (hz : z ∈ Z) : ∃ α β : ℕ, z = a ^ α * b ^ β := by
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [hinf, Subgroup.card_bot, mul_one, card_zpowers_of_pow_three ha3 ha1,
    card_zpowers_of_pow_three hb3 hb1] at hcard
  have heq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = Z :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr haZ)
      (Subgroup.zpowers_le.mpr hbZ)) (by rw [hZ9, hcard])
  have hz' : z ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [heq]
    exact hz
  rw [hset] at hz'
  obtain ⟨u, hu, v, hv, rfl⟩ := hz'
  obtain ⟨α, rfl⟩ := exists_pow_eq_of_mem_zpowers hu
  obtain ⟨β, rfl⟩ := exists_pow_eq_of_mem_zpowers hv
  exact ⟨α, β, rfl⟩

theorem zpowers_inf_zpowers_eq_bot {a b : G} {M : Subgroup G} (ha3 : a ^ 3 = 1) (haM : a ∉ M)
    (hbM : b ∈ M) : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [← zpowers_inf_eq_bot ha3 haM]
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1,
    Subgroup.zpowers_le.mpr hbM (Subgroup.mem_inf.mp hz).2⟩

end Prod

section Main


theorem item138SN_of (h131 : Item131) (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local)
    (hK18 : KFacts.KS18M12)
    (hM12D : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Toolkit.M12ThreeLocalData X)
    (hKS : Step138KStr) : Item138SN := by
  intro G _ _ A c L E hH F hF hPGL hSyl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, hxE, hyF, hframe, hd1, hdL, hcF, h81, h9, hELd⟩ := exists_frame138 hH hF hPGL
  obtain ⟨e, K, heΩ, hK, heF, hec, heL, hKcase⟩ := hKS G A c L E hH hPGL F hF
  have hH' := hH
  obtain ⟨h, -, hcE, hE3, hE27, hEN, -, -, hC⟩ := hH'
  have hF' := hF
  obtain ⟨⟨hFEL, hF3, hF27, -, hFN⟩, hFL9⟩ := hF'
  set d := ⁅x, y⁆ with hd
  set P := E ⊔ F with hP
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEN' : E ≤ Subgroup.normalizer (F : Set G) :=
    le_sup_left.trans (le_normalizer_of_card le_sup_right hF27 h81)
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have hd3 : d ^ 3 = 1 := hframe.comm_pow_three
  have hdZ : d ∈ E ⊓ F := hframe.comm_mem
  have hL := h.mem_thetaComponentsAt
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  obtain ⟨π, p, f, Kf, _, hKf, hq, φ, -⟩ := hC
  have hq2 := two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) hKf hq φ
  have hZL := Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hKf hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZL
  have hcZ : c ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨hcE, hcF⟩
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have heZ : e ∈ E ⊓ F := Subgroup.mem_inf.mpr ⟨heE, heF⟩
  have he1 : e ≠ 1 := fun h1 => hec (h1 ▸ one_mem _)
  have hcd : Subgroup.zpowers c ⊓ Subgroup.zpowers d = ⊥ := zpowers_inf_zpowers_eq_bot hc3 hcL hdL
  have hed : Subgroup.zpowers e ⊓ Subgroup.zpowers d = ⊥ := zpowers_inf_zpowers_eq_bot he3 heL hdL
  have hcdc : c * d = d * c := hEab c hcE d (Subgroup.mem_inf.mp hdZ).1
  have hedc : e * d = d * e := hEab e heE d (Subgroup.mem_inf.mp hdZ).1
  have hZgen : ∀ z ∈ E ⊓ F, ∃ α β : ℕ, z = c ^ α * d ^ β := fun z hz =>
    exists_pow_mul_pow_of_card hcZ hdZ hcdc hc3 hc1 hd3 hd1 hcd h9 hz
  obtain ⟨α, β, hce⟩ := exists_pow_mul_pow_of_card heZ hdZ hedc he3 he1 hd3 hd1 hed h9 hcZ
  obtain ⟨α', β', hec'⟩ := hZgen e heZ
  have hβ' : ¬ 3 ∣ β' := by
    rintro ⟨m, rfl⟩
    apply hec
    rw [hec', pow_mul, hd3, one_pow, mul_one]
    exact pow_mem (Subgroup.mem_zpowers c) α'
  obtain ⟨d', t, hd'E, hd'L, hd'1, htL, htN, htd'⟩ := exists_inverting_of_hyp138 hH
  have hd'mem : d' ∈ Subgroup.zpowers d := hELd ▸ Subgroup.mem_inf.mpr ⟨hd'E, hd'L⟩
  have htd : t * d * t⁻¹ = d⁻¹ := by
    have hd'3 : d' ^ 3 = 1 := hE3.2 d' hd'E
    have hdd' : d ∈ Subgroup.zpowers d' := by
      have hle : Subgroup.zpowers d' ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hd'mem
      have heq : Subgroup.zpowers d' = Subgroup.zpowers d := Subgroup.eq_of_le_of_card_ge hle
        (by rw [card_zpowers_of_pow_three hd3 hd1, card_zpowers_of_pow_three hd'3 hd'1])
      rw [heq]
      exact Subgroup.mem_zpowers d
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hdd'
    rw [← hm, ← conj_zpow, htd', inv_zpow]
  have htc : t * c = c * t := hLc t htL
  have hFmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → F ≤ B → B = F :=
    fun B hB hFB =>
      eq_of_isElemAbelian_le_right hframe hd1 hxE hyF hE27 hF27 h9 hFN hEN' hcF hSyl hB hFB
  have hcFL : c ∉ F ⊓ L := fun hc => hcL (Subgroup.mem_inf.mp hc).2
  have hFLab : CFSG.Assembly.IsElemAbelian 3 (F ⊓ L) :=
    ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from
      hFab a (Subgroup.mem_inf.mp a.2).1 b (Subgroup.mem_inf.mp b.2).1)⟩⟩,
      fun z hz => hF3.2 z (Subgroup.mem_inf.mp hz).1⟩
  obtain ⟨-, hc27⟩ := isElemAbelian_zpowers_sup_of_card_nine hc3 hcFL le_rfl hFL9
    (fun z hz => hFLab.2 z hz) (fun z hz => (hLc z (Subgroup.mem_inf.mp hz).2).symm)
  have hFdec : F = Subgroup.zpowers c ⊔ (F ⊓ L) :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcF) inf_le_left)
      (by rw [hc27, hF27])).symm
  have hFcL : F ≤ Subgroup.zpowers c ⊔ L := hFdec ▸ sup_le_sup_left inf_le_right _
  have h3L : 3 ∣ Nat.card L := by
    have hL9 := factorization_card_three_of_hyp138 hH hPGL
    exact Nat.dvd_of_factorization_pos (by rw [hL9]; norm_num)
  have hLH : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    intro g hg
    have hgc : g * c * g⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hg c).mp (Subgroup.mem_zpowers c)
    have hL' := Sec11.map_conj_mem_thetaComponentsAt hc3 hL hgc
    have h3L' : 3 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact h3L
    have heq := eq_of_mem_thetaComponentsAt_of_maximal h.orderOf_eq hL hZL hFcL hF3
      (fun B hB hFB => (hFmax B hB hFB) ▸ le_rfl) hL' h3L'
    exact map_conj_eq_iff_mem_normalizer.mp heq
  have hPL : P ⊓ L = F ⊓ L := by
    have hL9 := factorization_card_three_of_hyp138 hH hPGL
    have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [h81]; norm_num)
    have hle := card_le_of_isPGroup (inf_le_right : P ⊓ L ≤ L) (hP3.to_le inf_le_left)
    rw [hL9] at hle
    refine (Subgroup.eq_of_le_of_card_ge (inf_le_inf_right L le_sup_right) ?_).symm
    rw [hFL9]
    simpa using hle
  have hNF : ∀ u ∈ Subgroup.normalizer (P : Set G), u * c = c * u →
      u ∈ Subgroup.normalizer (F : Set G) := by
    intro u huP huc
    have huL : u ∈ Subgroup.normalizer (L : Set G) :=
      hLH (centralizer_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr huc))
    apply mem_normalizer_of_map_le
    rintro _ ⟨z, hz, rfl⟩
    change u * z * u⁻¹ ∈ F
    have hz' : z ∈ Subgroup.zpowers c ⊔ (F ⊓ L) := hFdec ▸ hz
    have hle : Subgroup.zpowers c ⊔ (F ⊓ L) ≤
        (Subgroup.zpowers c ⊔ (F ⊓ L)).comap (MulAut.conj u).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · change u * c * u⁻¹ ∈ Subgroup.zpowers c ⊔ (F ⊓ L)
        rw [huc, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
      · intro w hw
        change u * w * u⁻¹ ∈ Subgroup.zpowers c ⊔ (F ⊓ L)
        have hw' : w ∈ P ⊓ L := hPL ▸ hw
        have h1 : u * w * u⁻¹ ∈ P ⊓ L := Subgroup.mem_inf.mpr
          ⟨(Subgroup.mem_normalizer_iff.mp huP w).mp (Subgroup.mem_inf.mp hw').1,
            (Subgroup.mem_normalizer_iff.mp huL w).mp (Subgroup.mem_inf.mp hw').2⟩
        rw [hPL] at h1
        exact Subgroup.mem_sup_right h1
    have := hle hz'
    rw [← hFdec] at this
    exact this
  obtain ⟨s, hsK, hsP, hsd, hsE⟩ : ∃ s : G, s ∈ K ∧ s ∈ Subgroup.normalizer (P : Set G) ∧
      s * d * s⁻¹ = d⁻¹ ∧ s ∉ Subgroup.normalizer (E : Set G) := by
    rcases hKcase with hPGLK | hM12K
    · exact exists_s_of_pgl h131 hspor hH hF hSyl hframe hxE hyF hd1 hdL hcF h81 h9 heΩ hK heF
        heL hce hPGLK
    · exact exists_s_of_m12 h131 hspor h414 hK18 hM12D hH hF hframe hxE hyF h81 h9 heΩ hK heF
        hM12K
  have hse : s * e = e * s := Subgroup.mem_centralizer_singleton_iff.mp
    ((Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1) hsK)
  have hsH : s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro hsH
    refine false_of_conj (α := α') hcd hd3 hd1 hsH hsd hβ' ?_
    rw [← hec', hse, mul_inv_cancel_right]
  have hs2c : s ^ 2 * c = c * s ^ 2 := by
    have hsd' : s * d⁻¹ * s⁻¹ = d := by
      rw [show s * d⁻¹ * s⁻¹ = (s * d * s⁻¹)⁻¹ by group, hsd, inv_inv]
    have h2d : s ^ 2 * d * (s ^ 2)⁻¹ = d := by
      rw [sq, show s * s * d * (s * s)⁻¹ = s * (s * d * s⁻¹) * s⁻¹ by group, hsd, hsd']
    have h2e : s ^ 2 * e * (s ^ 2)⁻¹ = e := by
      rw [sq, show s * s * e * (s * s)⁻¹ = s * (s * e * s⁻¹) * s⁻¹ by group, hse,
        mul_inv_cancel_right, hse, mul_inv_cancel_right]
    have h2c : s ^ 2 * c * (s ^ 2)⁻¹ = c := by
      rw [hce, show s ^ 2 * (e ^ α * d ^ β) * (s ^ 2)⁻¹ =
          (s ^ 2 * e * (s ^ 2)⁻¹) ^ α * (s ^ 2 * d * (s ^ 2)⁻¹) ^ β by
        rw [conj_pow, conj_pow]; group, h2e, h2d]
    calc s ^ 2 * c = s ^ 2 * c * (s ^ 2)⁻¹ * s ^ 2 := by group
      _ = c * s ^ 2 := by rw [h2c]
  have hs2F := hNF (s ^ 2) (pow_mem hsP 2) hs2c
  have hs2y : s * (s * y * s⁻¹) * s⁻¹ ∈ F := by
    have := (Subgroup.mem_normalizer_iff.mp hs2F y).mp hyF
    rwa [sq, show s * s * y * (s * s)⁻¹ = s * (s * y * s⁻¹) * s⁻¹ by group] at this
  have hσ := coord_of_sq hframe hd1 hxE hyF hE27 hF27 h9 hFN hEab hFab hsP hs2y
  exact exists_mem_normalizer_of_frame hframe hd1 hxE hyF hE27 hF27 h9 hFN hEab hFab hcZ hcd
    hZgen hsP hsH hsE hsd hσ htN htc htd

end Main

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
