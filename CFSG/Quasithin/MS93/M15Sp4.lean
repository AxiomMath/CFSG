module

public import CFSG.Quasithin.MS93.M15Cover
public import CFSG.Quasithin.MS93.M15Quot
public import CFSG.Quasithin.MS93.M15Omega5
public import CFSG.Quasithin.Vol2.Ch3B513NSpC

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall CFSG.Quasithin.B513N

section Sec

variable {F : Type} [Field F] [CharP F 2]

@[expose] def omega5ProjM :
    ↥(⊤ : Subgroup (Multiplicative ((Ix → F) × F))) →* Multiplicative (Ix → F) where
  toFun m := Multiplicative.ofAdd (Multiplicative.toAdd (m : Multiplicative ((Ix → F) × F))).1
  map_one' := rfl
  map_mul' _ _ := rfl

omit [CharP F 2] in
theorem omega5ProjM_ker :
    (omega5ProjM (F := F)).ker = (omega5Rad F).subgroupOf ⊤ := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun h1 => congrArg Multiplicative.toAdd h1, fun h1 => congrArg Multiplicative.ofAdd h1⟩

omit [CharP F 2] in
theorem omega5ProjM_surjective : Function.Surjective (omega5ProjM (F := F)) := by
  intro x
  exact ⟨⟨Multiplicative.ofAdd (Multiplicative.toAdd x, 0), Subgroup.mem_top _⟩, rfl⟩

@[expose] noncomputable def omega5SecEquiv :
    (↥(⊤ : Subgroup (Multiplicative ((Ix → F) × F))) ⧸ (omega5Rad F).subgroupOf ⊤) ≃*
      Multiplicative (Ix → F) :=
  (QuotientGroup.quotientMulEquivOfEq omega5ProjM_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ omega5ProjM_surjective)

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem omega5_coord {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : ↥(StatedSp 2 F) →* ↥L} (h : (FFModel.omega5 F (omega5Rad F)).RealizesVia L U Z π) :
    ∃ β : ↥U →* Multiplicative (Ix → F), Function.Surjective β ∧
      (∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z) ∧
      ∀ (γ : ↥(StatedSp 2 F)) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
        β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (natRepSp F γ (Multiplicative.toAdd (β u))) := by
  obtain ⟨-, -, -, -, -, hsec, -, β₀, hβs, hβk, hβe⟩ := h
  let e := (omega5SecEquiv (F := F))
  let β : ↥U →* Multiplicative (Ix → F) := e.toMonoidHom.comp β₀
  have hβ : ∀ u, β u = e (β₀ u) := fun _ => rfl
  refine ⟨β, fun x => ?_, fun u => ?_, fun γ u hu => ?_⟩
  · obtain ⟨q, hq⟩ := e.surjective x
    obtain ⟨u, hu⟩ := hβs q
    exact ⟨u, by rw [hβ, hu, hq]⟩
  · exact (e.map_eq_one_iff).trans (hβk u)
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ u)
    have h1 := hβe γ u m hu (Subgroup.mem_top _) hm.symm
    have h2 : β ⟨_, hu⟩ = e (QuotientGroup.mk ⟨_, Subgroup.mem_top _⟩) := congrArg e h1
    have h3 : β u = e (QuotientGroup.mk m) := congrArg e hm.symm
    rw [h2, h3]
    rfl

theorem card_le_of_omega5_realizesVia (hexp : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W))
    (U Z : Subgroup W) (hZU : Z ≤ U) (hZfix : ∀ z ∈ Z, ∀ x ∈ L, x z = z)
    (hinv : ∀ x ∈ L, ∀ v ∈ U, x v ∈ U) (hcomm : XMod.commOf ↥L U = U) {n : ℕ} (hn : 2 ≤ n)
    [Finite F] (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSp 2 F) →* ↥L}
    (hπ : (FFModel.omega5 F (omega5Rad F)).RealizesVia L U Z π) :
    Nat.card ↥Z ≤ 2 ^ n := by
  have : Finite ↥(StatedSp 2 F) := Subtype.finite
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨β, hβs, hβk, hβe⟩ := omega5_coord hπ
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSp 2 F)) hexp L U Z hZU hZfix hinv
    hcomm π hπ.1 (natRepSp F) β hβs hβk (fun γ v hv => hβe γ v hv)
  rwa [finrank_H1_dual_natRepSp F hF hn] at hcard

end Sec

section Case

theorem exists_ne_zero_ne_one {F : Type} [Field F] (hF : 2 < Nat.card F) :
    ∃ β : F, β ≠ 0 ∧ β ≠ 1 := by
  by_contra hne
  push Not at hne
  have hs : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · exact ⟨true, by simp [hne x hx]⟩
  have := Nat.card_le_card_of_surjective _ hs
  have h2 : Nat.card Bool = 2 := by simp
  omega

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

theorem sp4_case_large (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K) {n : ℕ} (hn : 2 ≤ n)
    (hS : BinaryNaturalSp4 K ⊤ (fixV K) n) :
    Nat.card (fixV K) ≤ 2 ^ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ Z ≤ omega5Rad F, (FFModel.omega5 F Z).Realizes K ⊤ ⊥ := by
  obtain ⟨F, iF, fF, hF, π, hπ⟩ := hS
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow hFc
  have hcomm : XMod.commOf ↥K (⊤ : Subgroup V) = ⊤ := (xmodCommOf_top_eq K).trans h.comm
  have hbd : Nat.card (fixV K) ≤ 2 ^ n := by
    have hπ' : (FFModel.nat (StatedSp 2 F)).Realizes K ⊤ (fixV K ⊓ ⊤) := by
      rw [inf_top_eq]
      exact ⟨π, hπ⟩
    have := card_fixV_le_of_sp4 hV K ⊤ (fun _ _ _ _ => Subgroup.mem_top _) hcomm hn hF hπ'
    rwa [inf_top_eq] at this
  refine ⟨hbd, F, iF, fF, hF, ?_⟩
  have hD := omega5_isActionModel (F := F) le_rfl
  have : Finite (FFModel.omega5 F (omega5Rad F)).Amb :=
    (inferInstance : Finite (Multiplicative ((Ix → F) × F)))
  have : Finite ↥(FFModel.omega5 F (omega5Rad F)).sec := Subtype.finite
  have h4 : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨β, hβ0, hβ1⟩ := exists_ne_zero_ne_one h4
  have hgen : ∀ m ∈ (FFModel.omega5 F (omega5Rad F)).sec, m ∈ Subgroup.closure
      {x | ∃ γ, ∃ y ∈ (FFModel.omega5 F (omega5Rad F)).sec,
        x = (FFModel.omega5 F (omega5Rad F)).act γ y * y⁻¹} := by
    intro m _
    refine Subgroup.closure_mono ?_ (omega5_gen hβ0 hβ1 m)
    rintro _ ⟨g, z, rfl⟩
    exact ⟨g, z, Subgroup.mem_top _, rfl⟩
  have hE2' : ∀ m : Multiplicative ((Ix → F) × F), m ^ 2 = 1 := by
    intro m
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, CharTwo.two_eq_zero,
      zero_smul]
  have hRc : Nat.card ↥((omega5Rad F).subgroupOf ⊤) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv, ← hF]
    have e : F ≃ ↥(omega5Rad F) :=
      { toFun := fun c => ⟨Multiplicative.ofAdd (0, c), rfl⟩
        invFun := fun x => (Multiplicative.toAdd x.1).2
        left_inv := fun _ => rfl
        right_inv := fun x => by
          obtain ⟨y, hy⟩ := x
          apply Subtype.ext
          apply Multiplicative.toAdd.injective
          exact Prod.ext (hy : (Multiplicative.toAdd y).1 = 0).symm rfl }
    exact (Nat.card_congr e).symm
  obtain ⟨N, hN, hR⟩ := exists_quotBy_of_realizes hD (fun γ m hm => omega5Act_rad γ hm) hgen
    (fun m _ => hE2' m)
    (fun W _ _ hW L Z π' hreal hZ hcommL =>
      le_trans (card_le_of_omega5_realizesVia hW L ⊤ Z le_top (fun z hz x hx => hZ hz x hx)
        (fun _ _ _ _ => Subgroup.mem_top _) hcommL hn hF hreal) (le_of_eq hRc.symm))
    hV (fun z hz => hz) h.comm ⟨_, omega5_realizesVia_of_nat hπ⟩
  exact ⟨N, hN, hR⟩

end Case

end CFSG.Quasithin.MS93
