module

public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424NonToralT
public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424TorusM
public import CFSG.GH74.GLS.Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14

variable {K : Type} [Field K] {π : Bool} {n : ℕ} {T : Type} [Group T]

theorem center_eq_bot (hK : PiField π 2 n K) (hq : ModThree π (2 ^ n)) (hn : 2 ≤ n)
    (M : LModel π 2 n K T) : Subgroup.center T = ⊥ := by
  have hq2 : 2 < 2 ^ n := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hZ := Sec13.center_projImage_slPi hK hq hq2
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨g, rfl⟩ := M.surjective t
  have hcen : projOf (slPi π 3 (2 ^ n) K) g ∈
      Subgroup.center (Assembly.RankThreeEven.projImage (slPi π 3 (2 ^ n) K)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨h, rfl⟩ := projOf_surjective (slPi π 3 (2 ^ n) K) w
    have hmu : M.μ h * M.μ g = M.μ g * M.μ h := Subgroup.mem_center_iff.mp ht (M.μ h)
    have h1 : M.μ (h * g * h⁻¹ * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hmu]
      group
    obtain ⟨c, hc⟩ := (M.ker_iff _).mp h1
    have hker : (h * g * h⁻¹ * g⁻¹) ∈ (projOf (slPi π 3 (2 ^ n) K)).ker :=
      (mem_ker_projOf _).mpr ⟨c, hc⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hker
    calc projOf (slPi π 3 (2 ^ n) K) h * projOf (slPi π 3 (2 ^ n) K) g =
        projOf (slPi π 3 (2 ^ n) K) h * projOf (slPi π 3 (2 ^ n) K) g *
          (projOf (slPi π 3 (2 ^ n) K) h)⁻¹ * (projOf (slPi π 3 (2 ^ n) K) g)⁻¹ *
          (projOf (slPi π 3 (2 ^ n) K) g * projOf (slPi π 3 (2 ^ n) K) h) := by group
      _ = projOf (slPi π 3 (2 ^ n) K) g * projOf (slPi π 3 (2 ^ n) K) h := by rw [hker, one_mul]
  rw [hZ, Subgroup.mem_bot] at hcen
  exact (Subgroup.mem_bot).mpr ((M.ker_iff g).mpr ((mem_ker_projOf g).mp
    (MonoidHom.mem_ker.mpr hcen)))

theorem nonToral_M {n : ℕ} (hn : 4 ≤ n) (h : Sec4.IsoLThreePi T 2 n)
    (Ā : Subgroup (Multiplicative (ZMod 3) × T)) (hĀe : CFSG.Assembly.IsElemAbelian 3 Ā)
    (hĀ27 : Nat.card Ā = 27)
    (hgen : Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) ⊔
      ⨆ (B : Subgroup (Multiplicative (ZMod 3) × T)) (_ : B ≤ Ā) (_ : Nat.card B = 9),
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set (Multiplicative (ZMod 3) × T))) = ⊤) :
    Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) ≤ Ā := by
  obtain ⟨π, K, _, hK, hq, ⟨M⟩⟩ := exists_lmodel (by omega : 1 ≤ n) h
  have := hK.finite
  have : Finite T := Finite.of_surjective M.μ M.surjective
  obtain ⟨hEe, hE9, hAeq⟩ := proj_data (by omega) h Ā hĀe hĀ27
  set E : Subgroup T := Ā.map (MonoidHom.snd (Multiplicative (ZMod 3)) T) with hE
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hmemA : ∀ e ∈ E, ((1 : Multiplicative (ZMod 3)), e) ∈ Ā := fun e he => by
    rw [hAeq]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, he⟩
  by_cases hnab : ∃ a b : ↥(slPi π 3 (2 ^ n) K), M.μ a ∈ E ∧ M.μ b ∈ E ∧ a * b ≠ b * a
  ·
    obtain ⟨a, b, ha, hb, hab⟩ := hnab
    intro m hm
    have hcenT : ∀ e ∈ E, m.2 * e = e * m.2 := fun e he =>
      (congrArg Prod.snd (Subgroup.mem_centralizer_iff.mp hm (1, e) (hmemA e he))).symm
    have hmE : m.2 ∈ E := centralizer_le_of_nonabelian hK hq M hEc ha hb hab hcenT
    rw [hAeq]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, hmE⟩
  ·
    exfalso
    have htor : ∀ a b : ↥(slPi π 3 (2 ^ n) K), M.μ a ∈ E → M.μ b ∈ E → a * b = b * a := by
      intro a b ha hb
      by_contra hne
      exact hnab ⟨a, b, ha, hb, hne⟩
    have hO : ∀ B : Subgroup (Multiplicative (ZMod 3) × T), B ≤ Ā → Nat.card B = 9 →
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set (Multiplicative (ZMod 3) × T))) ≤
          Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) := by
      intro B hBA hB9
      set O := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set (Multiplicative (ZMod 3) × T)))
        with hOdef
      set D : Subgroup T := B.map (MonoidHom.snd (Multiplicative (ZMod 3)) T) with hD
      set N : Subgroup T := O.map (MonoidHom.snd (Multiplicative (ZMod 3)) T) with hN
      have hDE : D ≤ E := Subgroup.map_mono hBA
      have hN3 : ¬ 3 ∣ Nat.card N := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        intro h3
        have h1 : Nat.card N ∣ Nat.card O := Subgroup.card_map_dvd O _
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (coprime_card_pPrimeCoreOf 3 _) (h3.trans h1)
      have hNC : N ≤ Subgroup.centralizer (D : Set T) := by
        rintro _ ⟨w, hw, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨b, hb, rfl⟩
        have hwC : w ∈ Subgroup.centralizer (B : Set (Multiplicative (ZMod 3) × T)) :=
          pPrimeCoreOf_le 3 _ hw
        exact congrArg Prod.snd (Subgroup.mem_centralizer_iff.mp hwC b hb)
      have hNnorm : Subgroup.centralizer (D : Set T) ≤ Subgroup.normalizer (N : Set T) := by
        intro h hh
        have h1 : ((1 : Multiplicative (ZMod 3)), h) ∈
            Subgroup.centralizer (B : Set (Multiplicative (ZMod 3) × T)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          refine Prod.ext (by simp) ?_
          exact Subgroup.mem_centralizer_iff.mp hh b.2 ⟨b, hb, rfl⟩
        have h2 := le_normalizer_pPrimeCoreOf 3
          (Subgroup.centralizer (B : Set (Multiplicative (ZMod 3) × T))) h1
        refine Subgroup.mem_normalizer_fintype fun t ht => ?_
        obtain ⟨w, hw, rfl⟩ := ht
        exact ⟨(1, h) * w * (1, h)⁻¹, (Subgroup.mem_normalizer_iff.mp h2 w).mp hw, rfl⟩
      have hNE : ∀ w ∈ N, ∀ e ∈ E, w * e = e * w := by
        have hcard : Nat.card D ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hDE
        have hD1 : Nat.card D ≠ 1 := by
          intro h1
          have hDbot : D = ⊥ := Subgroup.eq_bot_of_card_eq D h1
          have hBle : B ≤ (⊤ : Subgroup (Multiplicative (ZMod 3))).prod ⊥ := fun b hb =>
            Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by
              have : b.2 ∈ D := ⟨b, hb, rfl⟩
              rw [hDbot] at this
              exact this⟩
          have h2 := Subgroup.card_le_of_le hBle
          rw [card_top_prod, Subgroup.card_bot, hB9] at h2
          omega
        have hd : Nat.card D = 3 ∨ Nat.card D = 9 := by
          have hle : Nat.card D ≤ 9 := Nat.le_of_dvd (by norm_num) hcard
          have hpos : 0 < Nat.card D := Nat.card_pos
          generalize Nat.card D = d at hcard hD1 hle hpos ⊢
          interval_cases d <;> omega
        rcases hd with hd3 | hd9
        · obtain ⟨x, hxD, hx1⟩ : ∃ x ∈ D, x ≠ 1 := by
            by_contra hcon
            push Not at hcon
            have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr hcon
            rw [this, Subgroup.card_bot] at hd3
            omega
          have hxE : x ∈ E := hDE hxD
          have hx3 : x ^ 3 = 1 := hEe.2 x hxE
          have hord : orderOf x = 3 := by
            have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
            exact orderOf_eq_prime hx3 hx1
          have hDx : Subgroup.zpowers x = D :=
            Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxD)
              (by rw [Nat.card_zpowers, hord, hd3])
          have hCx : Subgroup.centralizer ({x} : Set T) = Subgroup.centralizer (D : Set T) := by
            rw [← hDx, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
          exact toral_core hn hK hq M hEe htor hxE hx1 (N := N) (by rw [hCx]; exact hNC)
            (by rw [hCx]; exact hNnorm) hN3
        · have hDeq : D = E := Subgroup.eq_of_le_of_card_ge hDE (by rw [hE9, hd9])
          intro w hw e he
          exact (Subgroup.mem_centralizer_iff.mp (hNC hw) e (hDeq ▸ he)).symm
      intro w hw
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      refine Prod.ext (mul_comm _ _) ?_
      exact (hNE w.2 ⟨w, hw, rfl⟩ a.2 ⟨a, ha, rfl⟩).symm
    have hle : Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) ⊔
        ⨆ (B : Subgroup (Multiplicative (ZMod 3) × T)) (_ : B ≤ Ā) (_ : Nat.card B = 9),
          pPrimeCoreOf 3 (Subgroup.centralizer (B : Set (Multiplicative (ZMod 3) × T))) ≤
        Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) :=
      sup_le le_rfl (iSup_le fun B => iSup_le fun hBA => iSup_le fun hB9 => hO B hBA hB9)
    have htop : ∀ m : Multiplicative (ZMod 3) × T,
        m ∈ Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) := fun m => by
      have : m ∈ (⊤ : Subgroup (Multiplicative (ZMod 3) × T)) := Subgroup.mem_top m
      rw [← hgen] at this
      exact hle this
    obtain ⟨e, he, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
      rw [this, Subgroup.card_bot] at hE9
      omega
    have hecen : e ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (congrArg Prod.snd (Subgroup.mem_centralizer_iff.mp (htop (1, g)) (1, e)
        (hmemA e he))).symm
    rw [center_eq_bot hK hq (by omega) M, Subgroup.mem_bot] at hecen
    exact he1 hecen

end CFSG.RankThree.PartTwo.Sec15.KS1424
