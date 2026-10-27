module

public import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1120Proof
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofKernel
import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProof
import CFSG.RankThree.PartTwo.Sec11.Item118

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Statements

@[expose] def Step1120V0Bar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} →
      g * s * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y ∧
        g * x ^ 3 * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y

@[expose] def Step1119CommG2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      (∃ q : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ aschbacherSolvableCore 3 Y) q) →
      ∃ v : G, v ∉ Subgroup.closure ({x ^ 9, v ^ 3} : Set G) ∧
        g ∈ Subgroup.normalizer ((Subgroup.closure {x ^ 9, v ^ 3} : Subgroup G) : Set G) ∧
        (∀ z ∈ sec11P R g ⊓ Y, (∀ w ∈ sec11P R g ⊓ Y, z * w = w * z) →
          z ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G)) ∧
        ∃ w ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G), (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = v * w

@[expose] def Step1119CommD4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      (∃ n : ℕ, Sec8.IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) n) →
      ∃ v : G, v ∉ Subgroup.closure ({x ^ 9, v ^ 3} : Set G) ∧
        g ∈ Subgroup.normalizer ((Subgroup.closure {x ^ 9, v ^ 3} : Subgroup G) : Set G) ∧
        (∀ z ∈ sec11P R g ⊓ Y, (∀ w ∈ sec11P R g ⊓ Y, z * w = w * z) →
          z ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G)) ∧
        ∃ w ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G), (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = v * w

@[expose] def Step1119CommL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) →
      ∃ v : G, v ∉ Subgroup.closure ({x ^ 9, v ^ 3} : Set G) ∧
        g ∈ Subgroup.normalizer ((Subgroup.closure {x ^ 9, v ^ 3} : Subgroup G) : Set G) ∧
        (∀ z ∈ sec11P R g ⊓ Y, (∀ w ∈ sec11P R g ⊓ Y, z * w = w * z) →
          z ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G)) ∧
        ∃ w ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G), (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = v * w

@[expose] def Step1119SymS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype →
      (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (A : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      r * a = a * r → s * a = a * s →
      ¬ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.zpowers s = Subgroup.zpowers c

@[expose] def Step1119SymC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      A ≤ (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype →
      (Subgroup.upperCentralSeries (sec11P R g) 2).map (sec11P R g).subtype ≤ R →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (A : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      r * a = a * r → s * a = a * s →
      ¬ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} →
      (∃ h ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
        h * c * h⁻¹ ∈ A ∧ h * c * h⁻¹ ∉ Subgroup.closure ({c, d} : Set G)) →
      ∃ (c' : G) (L' : Subgroup G) (a' : G) (R' Y' : Subgroup G) (x' s' r' g' : G),
        Sec11Big G A c' L' a' R' Y' d x' s' r' g' ∧
          Subgroup.normalizer ((sec11P R' g' : Subgroup G) : Set G) ≤
            Subgroup.normalizer ((Subgroup.closure {c', d} : Subgroup G) : Set G)

end Statements

namespace Item1119StepsProof

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_not_mem {P A : Subgroup G} {c d : G} (hcA : c ∈ A)
    (hNA : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G))
    (hNd : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hN : ¬ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G)) :
    ∃ h ∈ Subgroup.normalizer (P : Set G),
      h * c * h⁻¹ ∈ A ∧ h * c * h⁻¹ ∉ Subgroup.closure ({c, d} : Set G) := by
  rw [IsConcreteLE.not_le_iff_exists] at hN
  obtain ⟨h, hhP, hhcd⟩ := hN
  refine ⟨h, hhP, (Subgroup.mem_normalizer_iff.mp (hNA hhP) c).mp hcA, fun hmem => hhcd ?_⟩
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hle : Subgroup.closure ({c, d} : Set G) ≤
      (Subgroup.closure ({c, d} : Set G)).comap (MulAut.conj h).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change h * w * h⁻¹ ∈ _
    rcases hw with rfl | rfl
    · exact hmem
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
        ((Subgroup.mem_normalizer_iff.mp (hNd hhP) w).mp (Subgroup.mem_zpowers w))
  exact hle hz

theorem normalizer_le_normalizer_thetaQuotCentralizer (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((Sec4.thetaQuotCentralizer Y : Subgroup G) : Set G) :=
  fun _ hn => Subgroup.mem_normalizer_fintype fun _ hz =>
    Sec6.conj_mem_thetaQuotCentralizer hz hn

end Generic

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sec11K_ne_bot (h : Sec11Data G A c L a R Y d x s r g) : sec11K L a ≠ ⊥ := by
  obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
  exact fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)

theorem V0_le (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hsa : s * a = a * s) :
    Subgroup.closure ({s, a, x ^ 3} : Set G) ≤ R ∧
      Subgroup.closure ({s, a, x ^ 3} : Set G) ≤ Subgroup.centralizer ({a} : Set G) ∧
      Subgroup.closure ({s, a, x ^ 3} : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  have hRL := (Item1116Proof.le_centralizer_and_normalizer h45 h).2
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hx3Y : x ^ 3 ∈ Y := Item1119Proof.x_cube_mem_Y h45 h
  have hxa3 : a * x ^ 3 * a⁻¹ = x ^ 3 := (Item1119Proof.a_x_facts h45 h).1
  refine ⟨?_, ?_, ?_⟩ <;> rw [Subgroup.closure_le] <;> intro y hy <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy <;>
    rcases hy with rfl | rfl | rfl
  · exact hsR
  · exact haR
  · exact R.pow_mem hxR 3
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hsa
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc x ^ 3 * a = a * x ^ 3 * a⁻¹ * a := by rw [hxa3]
      _ = a * x ^ 3 := by group
  · exact h.toSec11Std.mem_normalizer_Y (sec11K_ne_bot h) (hRL hsR) hsa
  · refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hYC hz), mul_inv_cancel_right]
    exact hz
  · exact Subgroup.le_normalizer hx3Y

theorem mem_V0_of_mem_sup (h45 : Sec4.Item4_5) (h118 : Item118)
    (h : Sec11Data G A c L a R Y d x s r g) (hsa : s * a = a * s) {w : G} (hwR : w ∈ R)
    (hwa : w * a = a * w)
    (hw : w ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) ⊔ Sec4.thetaQuotCentralizer Y) :
    w ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) := by
  set V0 := Subgroup.closure ({s, a, x ^ 3} : Set G) with hV0
  obtain ⟨hV0R, hV0a, hV0Y⟩ := V0_le h45 h hsa
  have hle : V0 ≤ Subgroup.normalizer ((Sec4.thetaQuotCentralizer Y : Subgroup G) : Set G) :=
    hV0Y.trans (normalizer_le_normalizer_thetaQuotCentralizer Y)
  have hw' : w ∈ ((V0 ⊔ Sec4.thetaQuotCentralizer Y : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hw'
  obtain ⟨v, hv, z, hz, rfl⟩ := Set.mem_mul.mp hw'
  have hvR := hV0R hv
  have hva := Subgroup.mem_centralizer_singleton_iff.mp (hV0a hv)
  have hzR : z ∈ R := by
    have e : z = v⁻¹ * (v * z) := by group
    rw [e]
    exact R.mul_mem (R.inv_mem hvR) hwR
  have hza : z * a = a * z := by
    have e : z = v⁻¹ * (v * z) := by group
    have hva' : v⁻¹ * a = a * v⁻¹ := by
      calc v⁻¹ * a = v⁻¹ * (a * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * a) * v⁻¹ := by rw [hva]
        _ = a * v⁻¹ := by group
    rw [e]
    calc v⁻¹ * (v * z) * a = v⁻¹ * ((v * z) * a) := by group
      _ = v⁻¹ * (a * (v * z)) := by rw [hwa]
      _ = (v⁻¹ * a) * (v * z) := by group
      _ = a * (v⁻¹ * (v * z)) := by rw [hva']; group
  have hza' := mem_zpowers_a_of_mem_thetaQuotCentralizer_Y h45 h118 h hzR hza hz
  have haV0 : a ∈ V0 := Subgroup.subset_closure (by simp)
  exact V0.mul_mem hv (Subgroup.zpowers_le.mpr haV0 hza')

end Data

end Item1119StepsProof

section Provers

theorem step1119Comm_of (hG2 : Step1119CommG2) (hD4 : Step1119CommD4) (hL3 : Step1119CommL3) :
    Step1119Comm := by
  intro G _ _ A c L a R Y d x s r g hbig
  rcases hbig.isList with h | h | h
  · exact hG2 G A c L a R Y d x s r g hbig h
  · exact hD4 G A c L a R Y d x s r g hbig h
  · exact hL3 G A c L a R Y d x s r g hbig h

theorem step1119Sym_of (h1117 : Item1117) (hS : Step1119SymS) (hC : Step1119SymC) :
    Step1119Sym := by
  intro G _ _ A c L a R Y d x s r g hbig hA hZR hNA hNd hra hsa hN
  have hsc := hS G A c L a R Y d x s r g hbig hA hZR hNA hNd hra hsa hN
  have hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} := by
    intro hrs
    have h9 := (h1117 G A c L a R Y d x s r g hbig.toSec11Data hsc hrs).2
    have h9' := hbig.orderOf_x_gt
    omega
  exact hC G A c L a R Y d x s r g hbig hA hZR hNA hNd hra hsa hN hsc hrs
    (Item1119StepsProof.exists_conj_not_mem hbig.mem_A hNA hNd hN)

theorem step1120V0_of (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) (h48 : Sec4.Item4_8)
    (hbar : Step1120V0Bar) : Step1120V0 := by
  intro G _ _ A c L a R Y d x s r g hbig hrs
  have h := hbig.toSec11Data
  have h118 := item118_of h117 h45 h48
  have hsa : s * a = a * s := item1115_of_mhoV h45 h113 h117 G A c L a R Y d x s r g h
  obtain ⟨hs, hx⟩ := hbar G A c L a R Y d x s r g hbig hrs
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hgR := h.g_mem_normalizer
  have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)
  have hxa3 : a * x ^ 3 * a⁻¹ = x ^ 3 := (Item1119Proof.a_x_facts h45 h).1
  have hx3a : x ^ 3 * a = a * x ^ 3 := by
    calc x ^ 3 * a = a * x ^ 3 * a⁻¹ * a := by rw [hxa3]
      _ = a * x ^ 3 := by group
  have hconj : ∀ y : G, y * a = a * y → (g * y * g⁻¹) * a = a * (g * y * g⁻¹) := by
    intro y hy
    have hga' : g⁻¹ * a = a * g⁻¹ := by
      calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * a) * g⁻¹ := by rw [hga]
        _ = a * g⁻¹ := by group
    calc g * y * g⁻¹ * a = g * y * (g⁻¹ * a) := by group
      _ = g * (y * a) * g⁻¹ := by rw [hga']; group
      _ = g * (a * y) * g⁻¹ := by rw [hy]
      _ = (g * a) * y * g⁻¹ := by group
      _ = a * (g * y * g⁻¹) := by rw [hga]; group
  have hgs : g * s * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) :=
    Item1119StepsProof.mem_V0_of_mem_sup h45 h118 h hsa
      ((Subgroup.mem_normalizer_iff.mp hgR s).mp hsR) (hconj s hsa) hs
  have hgx : g * x ^ 3 * g⁻¹ ∈ Subgroup.closure ({s, a, x ^ 3} : Set G) :=
    Item1119StepsProof.mem_V0_of_mem_sup h45 h118 h hsa
      ((Subgroup.mem_normalizer_iff.mp hgR _).mp (R.pow_mem hxR 3)) (hconj _ hx3a) hx
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hle : Subgroup.closure ({s, a, x ^ 3} : Set G) ≤
      (Subgroup.closure ({s, a, x ^ 3} : Set G)).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change g * y * g⁻¹ ∈ _
    rcases hy with rfl | rfl | rfl
    · exact hgs
    · rw [hga, mul_inv_cancel_right]
      exact Subgroup.subset_closure (by simp)
    · exact hgx
  exact hle hz

end Provers

end CFSG.RankThree.PartTwo.Sec11
