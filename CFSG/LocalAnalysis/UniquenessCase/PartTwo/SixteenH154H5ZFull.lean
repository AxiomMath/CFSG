module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [CommGroup V]

private def s16h_natHom (d : ℕ) (K : Type*) [Field K] :
    GL (Fin d) K →* MulAut (Multiplicative (Fin d → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd
        ((g : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd
        (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      left_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]

private theorem s16h_natHom_apply (d : ℕ) (K : Type*) [Field K] (g : GL (Fin d) K)
    (v : Multiplicative (Fin d → K)) :
    s16h_natHom d K g v =
      Multiplicative.ofAdd ((g : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v)) :=
  rfl

private theorem s16h_natHom_surjective (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = 2) : Function.Surjective (s16h_natHom 3 K) := by
  intro f
  let fA : (Fin 3 → K) ≃+ (Fin 3 → K) :=
    (AddEquiv.toMultiplicative (G := Fin 3 → K) (H := Fin 3 → K)).symm f
  have hfA : ∀ v : Fin 3 → K, f (Multiplicative.ofAdd v) = Multiplicative.ofAdd (fA v) :=
    fun _ => rfl
  have htwo : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
      exact (hy c hc).trans (hy 1 one_ne_zero).symm
  have hsmul : ∀ (c : K) (v : Fin 3 → K), fA (c • v) = c • fA v := by
    intro c v
    rcases htwo c with rfl | rfl <;> simp
  let gLin : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := fA, map_add' := fA.map_add, map_smul' := hsmul }
  let e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
    LinearEquiv.mk gLin fA.symm fA.left_inv fA.right_inv
  let g : LinearMap.GeneralLinearGroup K (Fin 3 → K) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv e
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm g, ?_⟩
  apply MulEquiv.ext
  intro x
  rw [s16h_natHom_apply]
  have hfx : f x = Multiplicative.ofAdd (fA (Multiplicative.toAdd x)) :=
    hfA (Multiplicative.toAdd x)
  rw [hfx]
  congr 1
  have hA_lin : (Matrix.mulVecLin (Matrix.GeneralLinearGroup.toLin.symm g) :
      (Fin 3 → K) →ₗ[K] (Fin 3 → K)) = gLin := by
    rw [← Matrix.GeneralLinearGroup.coe_toLin, MulEquiv.apply_symm_apply]
    rfl
  have hx := congrArg
    (fun (l : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) => l (Multiplicative.toAdd x)) hA_lin
  simpa [gLin, Matrix.mulVecLin_apply] using hx

theorem s16h_binarySL3_autSec_eq_top {L : Subgroup (MulAut V)} {I Z : Subgroup V}
    (h : BinaryNaturalSL L I Z 3 1) : autSec L I Z = ⊤ := by
  obtain ⟨K, hKfield, hKfin, hKcard, hReal⟩ := h
  letI := hKfield
  letI := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨π₀, hπ⟩ := hReal
  let π : ↥(StatedSL 3 K) →* ↥L := π₀
  let R : SzN15.NatReal L I Z (StatedSL 3 K) π := SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  have hLI : L ≤ stabSub I := by
    intro l hl
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
        have h1 := R.U_inv ((⟨l, hl⟩ : ↥L)⁻¹) ((l : MulAut V) u) hu
        simpa using h1,
      fun hu => R.U_inv ⟨l, hl⟩ u hu⟩
  have hLZ : L ≤ stabSub Z := by
    intro l hl
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
        have h1 := R.Z_inv ((⟨l, hl⟩ : ↥L)⁻¹) ((l : MulAut V) u) hu
        simpa using h1,
      fun hu => R.Z_inv ⟨l, hl⟩ u hu⟩
  have hle : Z.subgroupOf I ≤ β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    exact (hβk u).mpr (Subgroup.mem_subgroupOf.mp hu)
  let β₀ : Sec I Z →* Multiplicative (Fin 3 → K) :=
    QuotientGroup.lift (Z.subgroupOf I) β hle
  have hβ₀_mk : ∀ u : ↥I, β₀ (QuotientGroup.mk u : Sec I Z) = β u := by
    intro u
    rw [QuotientGroup.lift_mk']
  have hβ₀_inj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [MonoidHom.mem_ker, hβ₀_mk u] at hx
      have huZ : (u : V) ∈ Z := (hβk u).mp hx
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact huZ
  have hβ₀_surj : Function.Surjective β₀ := by
    intro y
    obtain ⟨u, hu⟩ := hβs y
    exact ⟨QuotientGroup.mk u, by rw [hβ₀_mk u]; exact hu⟩
  let βe : Sec I Z ≃* Multiplicative (Fin 3 → K) :=
    MulEquiv.ofBijective β₀ ⟨hβ₀_inj, hβ₀_surj⟩
  have hβe_mk : ∀ u : ↥I, βe (QuotientGroup.mk u : Sec I Z) = β u := hβ₀_mk
  have hβe_symm : ∀ u : ↥I, βe.symm (β u) = (QuotientGroup.mk u : Sec I Z) := by
    intro u
    rw [← hβe_mk u, MulEquiv.symm_apply_apply]
  rw [← B5.range_secHom L hLI hLZ, eq_top_iff]
  intro φ _
  rw [MonoidHom.mem_range]
  let f : MulAut (Multiplicative (Fin 3 → K)) := βe.symm.trans (φ.trans βe)
  have hf : ∀ y, f y = βe (φ (βe.symm y)) := fun _ => rfl
  obtain ⟨A, hA⟩ := s16h_natHom_surjective K hK2 f
  haveI : Finite Kˣ :=
    Finite.of_injective (fun u : Kˣ => (u : K)) (fun _ _ h => Units.ext h)
  have hunits : Nat.card Kˣ = 1 := by simp [Nat.card_units, hK2]
  haveI : Subsingleton Kˣ := Finite.card_le_one_iff_subsingleton.mp hunits.le
  have hAdet : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
    simpa using congrArg Units.val h1
  have hAmem : A ∈ StatedSL 3 K := Subgroup.subset_closure hAdet
  let γ : ↥(StatedSL 3 K) := ⟨A, hAmem⟩
  let l : ↥L := π γ
  refine ⟨l, ?_⟩
  have hnat : ∀ y, natAct (StatedSL 3 K) γ y = s16h_natHom 3 K A y := fun _ => rfl
  apply MulEquiv.ext
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  apply βe.injective
  calc βe (B5.secHom L hLI hLZ l (QuotientGroup.mk u))
      = β ⟨(l : MulAut V) (u : V), (hLI l.2 u).2 u.2⟩ := by
        rw [B5.secHom_mk, hβe_mk]
    _ = natAct (StatedSL 3 K) γ (β u) := hβe γ u ((hLI l.2 u).2 u.2)
    _ = s16h_natHom 3 K A (β u) := hnat (β u)
    _ = f (β u) := by rw [hA]
    _ = βe (φ (βe.symm (β u))) := hf _
    _ = βe (φ (QuotientGroup.mk u)) := by rw [hβe_symm u]

theorem s16h_binarySL3_faithful {L : Subgroup (MulAut V)} {I Z : Subgroup V}
    (h : BinaryNaturalSL L I Z 3 1) : L ⊓ centSec I Z = ⊥ := by
  obtain ⟨K, hKfield, hKfin, hKcard, hReal⟩ := h
  letI := hKfield
  letI := hKfin
  obtain ⟨π₀, hπ⟩ := hReal
  let π : ↥(StatedSL 3 K) →* ↥L := π₀
  let R : SzN15.NatReal L I Z (StatedSL 3 K) π := SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_inf] at ha
  obtain ⟨haL, haC⟩ := ha
  rw [mem_centSec] at haC
  obtain ⟨haStab, haZ⟩ := haC
  rw [Subgroup.mem_bot]
  obtain ⟨γ, hγ⟩ := R.surj ⟨a, haL⟩
  have hγval : ((π γ : ↥L) : MulAut V) = a := by rw [hγ]
  have hact : ∀ u : ↥I, natAct (StatedSL 3 K) γ (β u) = β u := by
    intro u
    have huI : a (u : V) ∈ I := (haStab (u : V)).2 u.2
    have hmem : β ⟨a (u : V), huI⟩ = natAct (StatedSL 3 K) γ (β u) := by
      have h := hβe γ u (R.U_inv (π γ) u u.2)
      simpa [hγval] using h
    have hz : a (u : V) * (u : V)⁻¹ ∈ Z := haZ (u : V) u.2
    have h1 : β ⟨a (u : V) * (u : V)⁻¹, I.mul_mem huI (I.inv_mem u.2)⟩ = 1 :=
      (hβk _).2 hz
    have h2 : β ⟨a (u : V), huI⟩ = β u := by
      have h3 : (⟨a (u : V) * (u : V)⁻¹, I.mul_mem huI (I.inv_mem u.2)⟩ : ↥I) *
          (⟨(u : V), u.2⟩ : ↥I) = ⟨a (u : V), huI⟩ :=
        Subtype.ext (by simp [mul_assoc])
      calc β ⟨a (u : V), huI⟩
          = β ((⟨a (u : V) * (u : V)⁻¹, I.mul_mem huI (I.inv_mem u.2)⟩ : ↥I) *
              (⟨(u : V), u.2⟩ : ↥I)) := by rw [← h3]
        _ = β (⟨a (u : V) * (u : V)⁻¹, I.mul_mem huI (I.inv_mem u.2)⟩ : ↥I) * β u := by
            rw [map_mul]
        _ = 1 * β u := by rw [h1]
        _ = β u := one_mul _
    rw [← hmem, h2]
  have hγ1 : γ = 1 := by
    refine natAct_faithful (StatedSL 3 K) γ (fun m => ?_)
    obtain ⟨u, rfl⟩ := hβs m
    rw [hact u, mul_inv_cancel]
  have : (⟨a, haL⟩ : ↥L) = 1 := by
    rw [← hγ, hγ1]
    exact map_one π
  exact congrArg Subtype.val this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
