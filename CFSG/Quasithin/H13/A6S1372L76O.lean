module

public import CFSG.Quasithin.Background.A7Q528Split
public import CFSG.Quasithin.Background.B5FinS8Core
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge Matrix CFSG.ComponentClassification.PresentationLocal

namespace A6L76O

@[expose] def alt8 (σ : Perm (Fin 8)) (h : Perm.sign σ = 1) : alternatingGroup (Fin 8) :=
  ⟨σ, Perm.mem_alternatingGroup.2 h⟩

@[expose] def t8 : alternatingGroup (Fin 8) := carmichaelCycle ⟨2, by decide⟩

@[expose] def h8 (k : CarmichaelIndex 8) : alternatingGroup (Fin 8) :=
  if k.1 = 3 then alt8 (swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7) (by decide)
  else if k.1 = 4 then alt8 (swap 0 3 * swap 1 5 * swap 2 6 * swap 4 7) (by decide)
  else if k.1 = 5 then alt8 (swap 0 3 * swap 1 4 * swap 2 6 * swap 5 7) (by decide)
  else alt8 (swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7) (by decide)

theorem chain8 : ∀ k : CarmichaelIndex 8, k.1 ≠ 2 →
    (carmichaelCycle k * t8 * (carmichaelCycle k)⁻¹) ^ 3 = 1 ∧
    (carmichaelCycle k * t8 * (carmichaelCycle k)⁻¹) * (h8 k * t8 * (h8 k)⁻¹) =
      (h8 k * t8 * (h8 k)⁻¹) * (carmichaelCycle k * t8 * (carmichaelCycle k)⁻¹) ∧
    (h8 k * t8 * (h8 k)⁻¹) ^ 3 = 1 ∧
    (h8 k * t8 * (h8 k)⁻¹) * t8 = t8 * (h8 k * t8 * (h8 k)⁻¹) := by
  decide +kernel

theorem t8_eq {k : CarmichaelIndex 8} (hk : k.1 = 2) : carmichaelCycle k = t8 := by
  have : k = ⟨2, by decide⟩ := Subtype.ext hk
  rw [this]
  rfl

theorem t8_pow_three : t8 ^ 3 = 1 := carmichaelCycle_pow_three _

section Split

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) (alternatingGroup (Fin 8)) M}

theorem inv_of_gen8 {C : Submodule (ZMod 2) M}
    (h : ∀ k, ∀ c ∈ C, ρ (carmichaelCycle k) c ∈ C) : ∀ g, ∀ c ∈ C, ρ g c ∈ C := by
  let T : Subgroup (alternatingGroup (Fin 8)) :=
    { carrier := {g | ∀ c ∈ C, ρ g c ∈ C}
      mul_mem' := fun {a b} ha hb c hc => by
        rw [map_mul, Module.End.mul_apply]
        exact ha _ (hb c hc)
      one_mem' := fun c hc => by rwa [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha c hc => by
        let f : C → C := fun x => ⟨ρ a x, ha x x.2⟩
        have hf : Function.Injective f := fun x y hxy => Subtype.ext (by
          have h1 := congrArg (fun z : C => ρ a⁻¹ (z : M)) hxy
          simpa [f] using h1)
        obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨c, hc⟩
        have h1 : ρ a y = c := congrArg Subtype.val hy
        rw [← h1, Representation.inv_self_apply]
        exact y.2 }
  have hT : (⊤ : Subgroup (alternatingGroup (Fin 8))) ≤ T := by
    rw [← closure_range_carmichaelCycle (by norm_num : 3 ≤ 8), Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact h k
  intro g c hc
  exact hT (Subgroup.mem_top g) c hc

theorem eq_bot_of_split8 {U : Submodule (ZMod 2) M} (hU : ∀ g, ∀ u ∈ U, ρ g u = u)
    (hfpf : ∀ v, ρ t8 v - v ∈ U → v ∈ U)
    (hspan : ∀ C : Submodule (ZMod 2) M, (∀ g v, ρ g v - v ∈ C) → C = ⊤) : U = ⊥ := by
  have hinvU : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => (hU g u hu).symm ▸ hu
  let C : Submodule (ZMod 2) M := LinearMap.range (ρ t8 - 1)
  have hmemC : ∀ v, ρ t8 v - v ∈ C := fun v => LinearMap.mem_range.mpr ⟨v, rfl⟩
  have hCt : ∀ c ∈ C, ∃ w, c = ρ t8 w - w := by
    intro c hc
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hc
    exact ⟨w, rfl⟩
  have hgen : ∀ k, ∀ c ∈ C, ρ (carmichaelCycle k) c ∈ C := by
    intro k c hc
    obtain ⟨w, rfl⟩ := hCt c hc
    by_cases hk : k.1 = 2
    · rw [t8_eq hk, map_sub]
      exact hmemC (ρ t8 w)
    · obtain ⟨hs3, hc1, hd3, hc2⟩ := chain8 k hk
      have e : ρ (carmichaelCycle k * t8 * (carmichaelCycle k)⁻¹) (ρ (carmichaelCycle k) w) =
          ρ (carmichaelCycle k) (ρ t8 w) := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul,
          Module.End.mul_apply]
      rw [map_sub, ← e]
      have hfd := A7Q528.fpf_conj hinvU hfpf (h8 k)
      obtain ⟨w1, hw1⟩ := A7Q528.exists_sub_eq_of_comm hU hs3 hfd hc1 (ρ (carmichaelCycle k) w)
      obtain ⟨w2, hw2⟩ := A7Q528.exists_sub_eq_of_comm hU hd3 hfpf hc2 w1
      rw [hw1, hw2]
      exact hmemC w2
  have hinv : ∀ g, ∀ c ∈ C, ρ g c ∈ C := inv_of_gen8 hgen
  have hall : ∀ g v, ρ g v - v ∈ C := by
    intro g v
    set n := v + ρ t8 v + ρ t8 (ρ t8 v) with hn
    have hρt3 : ρ t8 (ρ t8 (ρ t8 v)) = v := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← pow_three',
        t8_pow_three, map_one, Module.End.one_apply]
    have hnU : n ∈ U := by
      apply hfpf n
      have : ρ t8 n = n := by
        rw [hn, map_add, map_add, hρt3]
        abel
      rw [this, sub_self]
      exact U.zero_mem
    have hv : v = n + (ρ t8 (ρ t8 v) - ρ t8 v) := by
      have h2 := A7Q528.add_self_eq_zero₂ (ρ t8 (ρ t8 v))
      rw [hn]
      calc v = v + (ρ t8 (ρ t8 v) + ρ t8 (ρ t8 v)) := by rw [h2, add_zero]
        _ = v + ρ t8 v + ρ t8 (ρ t8 v) + (ρ t8 (ρ t8 v) - ρ t8 v) := by abel
    have e : ρ g v - v = ρ g (ρ t8 (ρ t8 v) - ρ t8 v) - (ρ t8 (ρ t8 v) - ρ t8 v) := by
      conv_lhs => rw [hv, map_add, hU g n hnU]
      abel
    rw [e]
    exact C.sub_mem (hinv g _ (hmemC _)) (hmemC _)
  have hC := hspan C hall
  rw [eq_bot_iff]
  intro u hu
  have huC : u ∈ C := hC ▸ Submodule.mem_top
  obtain ⟨w, rfl⟩ := hCt u huC
  rw [Submodule.mem_bot]
  exact A7Q528.sub_eq_zero_of_mem hU t8_pow_three hu

end Split

@[expose] noncomputable def eps {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    F ≃+* ZMod 2 :=
  haveI := Fintype.ofFinite F
  (ZMod.ringEquivOfPrime F Nat.prime_two (by rw [Fintype.card_eq_nat_card, hF])).symm

@[expose] noncomputable def slMap {d : ℕ} {F : Type} [Field F] (e : ZMod 2 ≃+* F) :
    ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)) →*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL d F) :=
  ((Matrix.GeneralLinearGroup.map e.toRingHom).comp
    (CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)).subtype).codRestrict _ fun g => by
    apply Subgroup.subset_closure
    have hg : ((g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det (g : GL (Fin d) (ZMod 2)) = 1 :=
        Subsingleton.elim _ _
      have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
      simpa using h2
    show (e.toRingHom.mapMatrix ((g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2))).det
      = 1
    rw [← RingHom.map_det, hg, map_one]

theorem slMap_val {d : ℕ} {F : Type} [Field F] (e : ZMod 2 ≃+* F)
    (g : ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2))) :
    (((slMap e g : ↥(CFSG.Assembly.LowTwoRank.StatedSL d F)) : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) =
      ((g : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)).map e := rfl

theorem slMap_surjective {d : ℕ} {F : Type} [Field F] (e : ZMod 2 ≃+* F) :
    Function.Surjective (slMap (d := d) e) := by
  intro g
  have hm : ∀ g' : ↥(CFSG.Assembly.LowTwoRank.StatedSL d F),
      ((g' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map e.symm ∈
        {A : Matrix (Fin d) (Fin d) (ZMod 2) | A.det = 1} := fun g' => by
    have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map e.symm.toRingHom
        (g' : GL (Fin d) F)) = 1 := Subsingleton.elim _ _
    have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
    simpa using h2
  refine ⟨⟨Matrix.GeneralLinearGroup.map e.symm.toRingHom (g : GL (Fin d) F),
    Subgroup.subset_closure (hm g)⟩, Subtype.ext (Units.ext ?_)⟩
  show (((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map e.symm).map e =
    ((g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  ext i j
  simp

theorem realizesVia_zmod {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)} {U Z : Subgroup V}
    {d : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {π : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL d F)).Gam →* ↥Y}
    (h : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL d F)).RealizesVia Y U Z π) :
    ∃ π' : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2))).Gam →* ↥Y,
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2))).RealizesVia Y U Z π' := by
  set e : ZMod 2 ≃+* F := (eps hF).symm with he
  let Ê : ↥(FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2))).sec →*
      ↥(FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL d F)).sec :=
    { toFun := fun m => ⟨Multiplicative.ofAdd
        (fun i => e (Multiplicative.toAdd (show Multiplicative (Fin d → ZMod 2) from m.1) i)),
        Subgroup.mem_top _⟩
      map_one' := Subtype.ext (by
        show Multiplicative.ofAdd (fun i => e ((0 : Fin d → ZMod 2) i)) = 1
        funext i
        simp
        rfl)
      map_mul' := fun a b => Subtype.ext (by
        show Multiplicative.ofAdd (fun i => e ((Multiplicative.toAdd
            (show Multiplicative (Fin d → ZMod 2) from a.1) +
          Multiplicative.toAdd (show Multiplicative (Fin d → ZMod 2) from b.1)) i)) = _
        funext i
        simp only [Pi.add_apply, map_add]
        rfl) }
  have hÊ : Function.Surjective Ê := by
    intro m
    refine ⟨⟨Multiplicative.ofAdd (fun i => e.symm (Multiplicative.toAdd
      (show Multiplicative (Fin d → F) from m.1) i)), Subgroup.mem_top _⟩, Subtype.ext ?_⟩
    show Multiplicative.ofAdd (fun i => e (e.symm (Multiplicative.toAdd
      (show Multiplicative (Fin d → F) from m.1) i))) = m.1
    simp only [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨π.comp (slMap e), FFModel.RealizesVia.of_surjHom (FFModel.nat_isActionModel _) h
    (slMap e) (slMap_surjective e) Ê hÊ ?_ ?_⟩
  · intro σ m hm
    apply Multiplicative.toAdd.injective
    funext i
    exact RingHom.map_mulVec e.toRingHom _ _ i
  · intro m
    constructor
    · intro hm
      have h1 : (show Multiplicative (Fin d → F) from (Ê m).1) = 1 := (Subgroup.mem_bot).1 hm
      apply (Subgroup.mem_bot).2
      show (show Multiplicative (Fin d → ZMod 2) from m.1) = 1
      apply Multiplicative.toAdd.injective
      funext i
      have h2 := congrFun (congrArg Multiplicative.toAdd h1) i
      exact e.injective (h2.trans (map_zero e).symm)
    · intro hm
      have h1 : (show Multiplicative (Fin d → ZMod 2) from m.1) = 1 := (Subgroup.mem_bot).1 hm
      apply (Subgroup.mem_bot).2
      show Multiplicative.ofAdd (fun i => e (Multiplicative.toAdd
        (show Multiplicative (Fin d → ZMod 2) from m.1) i)) = 1
      rw [h1]
      funext i
      simp
      rfl

theorem mk_inj_nat {n : ℕ} {K : Type} [Field K] {Γ : Subgroup (GL (Fin n) K)}
    {a b : ↥(FFModel.nat Γ).sec}
    (h : (QuotientGroup.mk a : ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf
      (FFModel.nat Γ).sec) = QuotientGroup.mk b) : a = b := by
  rw [QuotientGroup.eq] at h
  have h' : (show Multiplicative (Fin n → K) from (a⁻¹ * b : ↥(FFModel.nat Γ).sec).1) = 1 :=
    (Subgroup.mem_bot).1
      (Subgroup.mem_subgroupOf.1 h : _ ∈ (⊥ : Subgroup (Multiplicative (Fin n → K))))
  exact inv_mul_eq_one.1 (Subtype.ext h')

theorem l42_fpf : ∀ x : Fin 4 → ZMod 2,
    (CFSG.GH74.Exceptional.l42Mat 0) *ᵥ x = x → x = 0 := by
  decide

theorem alpha_t8 : (((B5FinS8.alpha t8 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) :
    GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = CFSG.GH74.Exceptional.l42Mat 0 := by
  rw [B5FinS8.coe_alpha, t8, B5FinS8.alphaHom_carmichaelCycle]
  rfl

end A6L76O

theorem kgSL4Split_holds :
    ∀ (V : Type) [CommGroup V] [Finite V] (Y : Subgroup (MulAut V)), (∀ v : V, v * v = 1) →
      commV Y = ⊤ → BinaryNaturalSL Y (commV Y) (fixV Y ⊓ commV Y) 4 1 → fixV Y = ⊥ := by
  intro V _ _ Y hV2 htop hBN
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add]
    exact hV2 (Additive.toMul x)
  obtain ⟨F, _, _, hF, π, hπ⟩ := hBN
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  obtain ⟨π', hπ'⟩ := A6L76O.realizesVia_zmod hF2 hπ
  obtain ⟨hπs, -, -, -, -, -, -, β, -, hβk, hβe⟩ := hπ'
  let θ : alternatingGroup (Fin 8) →* MulAut V := Y.subtype.comp (π'.comp B5FinS8.alpha)
  let ρ : Representation (ZMod 2) (alternatingGroup (Fin 8)) (Additive V) :=
    { toFun := fun σ => (AddMonoidHom.mk'
        (fun x : Additive V => Additive.ofMul (θ σ (Additive.toMul x)))
        (fun x y => by simp)).toZModLinearMap 2
      map_one' := by
        ext x
        simp
      map_mul' := fun s t => by
        ext x
        simp }
  have hρ : ∀ σ x, ρ σ x = Additive.ofMul (θ σ (Additive.toMul x)) := fun _ _ => rfl
  let U : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (fixV Y))
  have hmemU : ∀ x, x ∈ U ↔ Additive.toMul x ∈ fixV Y := fun x => Iff.rfl
  have hθY : ∀ σ, θ σ ∈ Y := fun σ => (π' (B5FinS8.alpha σ)).2
  have hU : ∀ g, ∀ u ∈ U, ρ g u = u := by
    intro g u hu
    rw [hρ]
    exact congrArg Additive.ofMul ((hmemU u).1 hu (θ g) (hθY g))
  have hfpf : ∀ v, ρ A6L76O.t8 v - v ∈ U → v ∈ U := by
    intro v hv
    rw [hmemU] at hv ⊢
    have hv' : θ A6L76O.t8 (Additive.toMul v) * (Additive.toMul v)⁻¹ ∈ fixV Y := by
      have h0 := hv
      rwa [toMul_sub, div_eq_mul_inv] at h0
    have hwC : Additive.toMul v ∈ commV Y := htop ▸ Subgroup.mem_top _
    have hθC : θ A6L76O.t8 (Additive.toMul v) ∈ commV Y := htop ▸ Subgroup.mem_top _
    have hcC : θ A6L76O.t8 (Additive.toMul v) * (Additive.toMul v)⁻¹ ∈ commV Y :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨_, hwC⟩)
    have h1 : β ⟨_, hθC⟩ = QuotientGroup.mk ⟨(FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4
        (ZMod 2))).act (B5FinS8.alpha A6L76O.t8) m.1, Subgroup.mem_top _⟩ :=
      hβe (B5FinS8.alpha A6L76O.t8) ⟨_, hwC⟩ m hθC (Subgroup.mem_top _) hm.symm
    have h2 : β ⟨_, hcC⟩ = 1 := (hβk _).2 ⟨hv', hcC⟩
    have h3 : β ⟨_, hθC⟩ = β ⟨_, hwC⟩ := by
      have e : (⟨_, hθC⟩ : ↥(commV Y)) = ⟨_, hcC⟩ * ⟨_, hwC⟩ :=
        Subtype.ext (inv_mul_cancel_right _ _).symm
      rw [e, map_mul, h2, one_mul]
    rw [h1, ← hm] at h3
    have h4 := A6L76O.mk_inj_nat h3
    have h5 := congrArg (fun z : ↥(FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4
      (ZMod 2))).sec => Multiplicative.toAdd (show Multiplicative (Fin 4 → ZMod 2) from z.1)) h4
    simp only at h5
    have h6 : (CFSG.GH74.Exceptional.l42Mat 0) *ᵥ
        Multiplicative.toAdd (show Multiplicative (Fin 4 → ZMod 2) from m.1) =
        Multiplicative.toAdd (show Multiplicative (Fin 4 → ZMod 2) from m.1) := by
      rw [← A6L76O.alpha_t8]
      exact h5
    have h7 := A6L76O.l42_fpf _ h6
    have h8 : m = 1 := Subtype.ext (show (show Multiplicative (Fin 4 → ZMod 2) from m.1) = 1 from
      toAdd_eq_zero.1 h7)
    have h9 : β ⟨_, hwC⟩ = 1 := by rw [← hm, h8, QuotientGroup.mk_one]
    exact ((hβk _).1 h9).1
  have hspan : ∀ C : Submodule (ZMod 2) (Additive V), (∀ g v, ρ g v - v ∈ C) → C = ⊤ := by
    intro C hC
    let C' : Subgroup V :=
      { carrier := {w | Additive.ofMul w ∈ C}
        one_mem' := C.zero_mem
        mul_mem' := fun ha hb => C.add_mem ha hb
        inv_mem' := fun ha => C.neg_mem ha }
    have hle : commV Y ≤ C' := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨y, hy, v, rfl⟩
      obtain ⟨σ', hσ'⟩ := hπs ⟨y, hy⟩
      obtain ⟨σ, rfl⟩ := B5FinS8.alpha_surjective σ'
      have hy' : θ σ = y := congrArg Subtype.val hσ'
      show Additive.ofMul (y v * v⁻¹) ∈ C
      have e : Additive.ofMul (y v * v⁻¹) = ρ σ (Additive.ofMul v) - Additive.ofMul v := by
        rw [← hy', hρ, ← div_eq_mul_inv, ofMul_div]
        rfl
      rw [e]
      exact hC σ (Additive.ofMul v)
    rw [eq_top_iff]
    intro x _
    exact hle (htop ▸ Subgroup.mem_top (Additive.toMul x))
  have hbot := A6L76O.eq_bot_of_split8 hU hfpf hspan
  rw [eq_bot_iff]
  intro w hw
  have h1 : Additive.ofMul w ∈ U := (hmemU _).2 hw
  rw [hbot, Submodule.mem_bot] at h1
  exact (Subgroup.mem_bot).2 (Additive.ofMul.injective h1)

end CFSG.Quasithin.H13.A6
