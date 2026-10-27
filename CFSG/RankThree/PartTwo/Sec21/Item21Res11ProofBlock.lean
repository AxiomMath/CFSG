module

public import CFSG.RankThree.PartTwo.KFacts.KS222U4OddModel
public import CFSG.RankThree.PartOne.CTP.Phan5Cent

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res11Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec21.U4OddLines
open CFSG.RankThree.PartOne.KFU (diagU diagU_val torusVec torusSU mem_torusSU_iff
  torusSU_le_unitarySU)
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open Matrix

section BlockMat

variable {F : Type*} [Field F] {m k i : ℕ}

theorem diagonal_mul_blockSel {d : Fin m → F} {μ : F}
    (hd : ∀ (a : Fin m) (j : Fin k), a.val = i + j.val → d a = μ) :
    diagonal d * blockSel F m k i = μ • blockSel F m k i := by
  ext a j
  rw [diagonal_mul, Matrix.smul_apply, blockSel_apply, smul_eq_mul]
  split_ifs with h
  · rw [hd a j h]
  · simp

theorem blockSel_transpose_mul_diagonal {d : Fin m → F} {μ : F}
    (hd : ∀ (a : Fin m) (j : Fin k), a.val = i + j.val → d a = μ) :
    (blockSel F m k i)ᵀ * diagonal d = μ • (blockSel F m k i)ᵀ := by
  ext j a
  rw [mul_diagonal, Matrix.smul_apply, transpose_apply, blockSel_apply, smul_eq_mul]
  split_ifs with h
  · rw [hd a j h, one_mul, mul_one]
  · simp

theorem blockMat_mul_diagonal {d : Fin m → F} {μ : F}
    (hd : ∀ (a : Fin m) (j : Fin k), a.val = i + j.val → d a = μ)
    (M : Matrix (Fin k) (Fin k) F) :
    blockMat m i M * diagonal d = diagonal d * blockMat m i M := by
  unfold blockMat
  set L := blockSel F m k i
  have h1 : L * (M - 1) * Lᵀ * diagonal d = μ • (L * (M - 1) * Lᵀ) := by
    rw [Matrix.mul_assoc, blockSel_transpose_mul_diagonal hd, Matrix.mul_smul]
  have h2 : diagonal d * (L * (M - 1) * Lᵀ) = μ • (L * (M - 1) * Lᵀ) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, diagonal_mul_blockSel hd, Matrix.smul_mul,
      Matrix.smul_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2]

theorem blockMat_diagonal_two (i : Fin 3) (a b : F) :
    blockMat 4 (i : ℕ) (diagonal ![a, b]) =
      diagonal (fun x : Fin 4 => if x = i.castSucc then a else if x = i.succ then b else 1) := by
  fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.sub_apply, Matrix.diagonal_apply]

end BlockMat

section Root

variable {K : Type} [Field K]

@[expose] def rootFun (ζ : Kˣ) (i : Fin 3) : Fin 4 → Kˣ := fun x =>
  if x = i.castSucc then ζ else if x = i.succ then ζ⁻¹ else 1

theorem rootFun_mem {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (i : Fin 3) : rootFun ζ i ∈ torusVec 3 4 K := by
  refine ⟨fun x => ?_, ?_⟩
  · simp only [rootFun]
    split_ifs <;> simp [hζ, inv_pow]
  · rw [Fin.prod_univ_four]
    fin_cases i <;> simp [rootFun]

@[expose] def rootVec (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (i : Fin 3) : torusVec 3 4 K :=
  ⟨rootFun ζ i, rootFun_mem hζ i⟩

theorem coe_rootVec (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (i : Fin 3) :
    ((rootVec ζ hζ i : torusVec 3 4 K) : Fin 4 → Kˣ) = rootFun ζ i := rfl

end Root

section Blocks

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {c : G} {n : ℕ} {K : Type}
  [Field K]

theorem exists_perfect_block (C : U4OddCtx G L A c n K) {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (i : Fin 3) :
    ∃ Λ : Subgroup G, Group.IsPerfect Λ ∧ Λ ≤ L ∧ C.theta (rootVec ζ hζ i) ∈ Λ ∧
      ∀ d : torusVec 3 4 K, (d : Fin 4 → Kˣ) i.castSucc = (d : Fin 4 → Kˣ) i.succ →
        Λ ≤ Subgroup.centralizer ({C.theta d} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := C.hU.finite
  have : CharP K 2 := C.hU.charP
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [C.hU.card, ← pow_mul, mul_comm]
  have hEq : CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution K 2 n)
      4 = unitarySU 2 n K 4 := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 4
  set ι : Su K 2 n 4 →* unitarySU 2 n K 4 := Subgroup.inclusion hEq.le with hι
  set h : Su K 2 n 2 →* G := C.phi.comp (ι.comp (blockEmb2 K 2 n 3 i)) with hh
  have : Group.IsPerfect (Su K 2 n 2) := CFSG.RankThree.PartOne.CTP.isPerfect_su_two hK C.hf2
  have hcoe : ∀ g : Su K 2 n 2, (((ι (blockEmb2 K 2 n 3 i g) : unitarySU 2 n K 4) :
      GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blockMat 4 (i : ℕ) (((g : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) := fun g => rfl
  refine ⟨h.range, Group.IsPerfect.range h, ?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact C.phi_mem_L _
  ·
    have hu : diagU ![ζ, ζ⁻¹] ∈
        CFSG.LieType.Universal.Unitary.SUid (CFSG.LieType.BorelTits.unitaryInvolution K 2 n) 2 := by
      rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2]
      refine torusSU_le_unitarySU C.hU C.hpq (mem_torusSU_iff.mpr ⟨![ζ, ζ⁻¹], fun x => ?_, ?_, rfl⟩)
      · fin_cases x <;> simp [hζ, inv_pow]
      · simp [Fin.prod_univ_two]
    refine ⟨⟨_, hu⟩, ?_⟩
    rw [hh, MonoidHom.comp_apply, MonoidHom.comp_apply, U4OddCtx.theta_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [hcoe, U4OddCtx.coe_torU, diagU_val, coe_rootVec]
    change blockMat 4 (i : ℕ) (diagonal fun x => ((![ζ, ζ⁻¹] x : Kˣ) : K)) = _
    have e : (fun x => ((![ζ, ζ⁻¹] x : Kˣ) : K)) = ![(ζ : K), ((ζ⁻¹ : Kˣ) : K)] := by
      funext x
      fin_cases x <;> rfl
    rw [e, blockMat_diagonal_two]
    congr 1
    funext x
    simp only [rootFun]
    split_ifs <;> rfl
  · intro d hd
    rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hh, MonoidHom.comp_apply, MonoidHom.comp_apply,
      U4OddCtx.theta_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hcoe, U4OddCtx.coe_torU, diagU_val]
    refine blockMat_mul_diagonal (μ := ((d : Fin 4 → Kˣ) i.castSucc : K)) (fun a j haj => ?_) _
    fin_cases j
    · have : a = i.castSucc := Fin.ext (by simpa using haj)
      rw [this]
    · have : a = i.succ := Fin.ext (by simp at haj; simp [haj])
      rw [this, hd]

theorem exists_root_not_mem (C : U4OddCtx G L A c n K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {E : Subgroup G} (hcE : c ∈ E) (hE : Nat.card E = 27) :
    ∃ i : Fin 3, C.theta (rootVec ζ hζ.pow_eq_one i) ∉ E := by
  by_contra! hall
  have hθ : ∀ d : torusVec 3 4 K, C.theta d ∈ E := by
    intro d
    have hd3 : ∀ x, ((d : Fin 4 → Kˣ) x) ^ 3 = 1 := d.2.1
    have hprod : ∏ x, (d : Fin 4 → Kˣ) x = 1 := d.2.2
    rw [Fin.prod_univ_four] at hprod
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_mem_rootsOfUnity
      (ξ := (d : Fin 4 → Kˣ) 0) ((mem_rootsOfUnity 3 _).mpr (hd3 0))
    obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_mem_rootsOfUnity
      (ξ := (d : Fin 4 → Kˣ) 0 * (d : Fin 4 → Kˣ) 1)
      ((mem_rootsOfUnity 3 _).mpr (by rw [mul_pow, hd3, hd3, one_mul]))
    obtain ⟨e, -, he⟩ := hζ.eq_pow_of_mem_rootsOfUnity
      (ξ := (d : Fin 4 → Kˣ) 0 * (d : Fin 4 → Kˣ) 1 * (d : Fin 4 → Kˣ) 2)
      ((mem_rootsOfUnity 3 _).mpr (by rw [mul_pow, mul_pow, hd3, hd3, hd3, one_mul, one_mul]))
    have hdeq : d = rootVec ζ hζ.pow_eq_one 0 ^ a * rootVec ζ hζ.pow_eq_one 1 ^ b *
        rootVec ζ hζ.pow_eq_one 2 ^ e := by
      apply Subtype.ext
      funext x
      fin_cases x
      · simp [rootVec, rootFun, ha]
      · simp only [rootVec, rootFun, Subgroup.coe_mul, Subgroup.coe_pow, Pi.mul_apply,
          Pi.pow_apply]
        simp only [Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one,
          Fin.succ_one_eq_two]
        simp [inv_pow, ha, hb]
      · simp only [rootVec, rootFun, Subgroup.coe_mul, Subgroup.coe_pow, Pi.mul_apply,
          Pi.pow_apply]
        simp [inv_pow, hb, he]
        group
      · have h3 : (d : Fin 4 → Kˣ) 3 =
            ((d : Fin 4 → Kˣ) 0 * (d : Fin 4 → Kˣ) 1 * (d : Fin 4 → Kˣ) 2)⁻¹ :=
          eq_inv_of_mul_eq_one_right hprod
        simp only [rootVec, rootFun, Subgroup.coe_mul, Subgroup.coe_pow, Pi.mul_apply,
          Pi.pow_apply]
        simp [inv_pow, he, h3]
    rw [hdeq, map_mul, map_mul, map_pow, map_pow, map_pow]
    exact E.mul_mem (E.mul_mem (E.pow_mem (hall 0) a) (E.pow_mem (hall 1) b))
      (E.pow_mem (hall 2) e)
  have hAE : A ≤ E := by
    intro x hx
    obtain ⟨d, j, rfl⟩ := C.decomp hx
    exact E.mul_mem (hθ d) (E.zpow_mem hcE j)
  have h1 := Subgroup.card_le_of_le hAE
  rw [C.hA81, hE] at h1
  norm_num at h1

theorem exists_mem_block (C : U4OddCtx G L A c n K) {F : Subgroup G} (hFA : F ≤ A)
    (hF : 3 < Nat.card F) (i : Fin 3) :
    ∃ f ∈ F, f ≠ 1 ∧ ∃ (d : torusVec 3 4 K) (k : ℤ),
      (d : Fin 4 → Kˣ) i.castSucc = (d : Fin 4 → Kˣ) i.succ ∧ f = C.theta d * c ^ k := by
  by_contra! hall
  have hdec : ∀ f : F, ∃ (d : torusVec 3 4 K) (k : ℤ), (f : G) = C.theta d * c ^ k :=
    fun f => C.decomp (hFA f.2)
  choose D Kk hDK using hdec
  let g : F → rootsOfUnity 3 K := fun f =>
    ⟨(D f : Fin 4 → Kˣ) i.castSucc * ((D f : Fin 4 → Kˣ) i.succ)⁻¹, by
      rw [mem_rootsOfUnity, mul_pow, inv_pow, (D f).2.1, (D f).2.1, inv_one, mul_one]⟩
  have hcomm : ∀ (d : torusVec 3 4 K) (j : ℤ), C.theta d * c ^ j = c ^ j * C.theta d :=
    fun d j => (Commute.zpow_right (show Commute (C.theta d) c from
      C.comm_c (C.theta_mem_L d)) j).eq
  have hinj : Function.Injective g := by
    intro f f' hff'
    by_contra hne
    have heq : (D f : Fin 4 → Kˣ) i.castSucc * ((D f : Fin 4 → Kˣ) i.succ)⁻¹ =
        (D f' : Fin 4 → Kˣ) i.castSucc * ((D f' : Fin 4 → Kˣ) i.succ)⁻¹ :=
      congrArg Subtype.val hff'
    have hmem : (f : G) * (f' : G)⁻¹ ∈ F := F.mul_mem f.2 (F.inv_mem f'.2)
    have hne1 : (f : G) * (f' : G)⁻¹ ≠ 1 := fun h => hne (Subtype.ext (mul_inv_eq_one.mp h))
    refine hall _ hmem hne1 (D f * (D f')⁻¹) (Kk f - Kk f') ?_ ?_
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply]
      rw [mul_inv_eq_iff_eq_mul] at heq ⊢
      rw [heq]
      ac_rfl
    · rw [hDK f, hDK f', map_mul, map_inv, _root_.zpow_sub]
      have h1 := hcomm (D f') (Kk f')
      have h2 := hcomm (D f') (Kk f)
      calc C.theta (D f) * c ^ Kk f * (C.theta (D f') * c ^ Kk f')⁻¹
          = C.theta (D f) * c ^ Kk f * (c ^ Kk f')⁻¹ * (C.theta (D f'))⁻¹ := by group
        _ = C.theta (D f) * (C.theta (D f'))⁻¹ * (c ^ Kk f * (c ^ Kk f')⁻¹) := by
          have h3 : (c ^ Kk f * (c ^ Kk f')⁻¹) * (C.theta (D f'))⁻¹ =
              (C.theta (D f'))⁻¹ * (c ^ Kk f * (c ^ Kk f')⁻¹) := by
            have h4 : Commute (C.theta (D f')) (c ^ Kk f * (c ^ Kk f')⁻¹) :=
              (Commute.mul_right (show Commute (C.theta (D f')) (c ^ Kk f) from h2)
                (show Commute (C.theta (D f')) (c ^ Kk f') from h1).inv_right)
            exact h4.inv_left.eq.symm
          calc C.theta (D f) * c ^ Kk f * (c ^ Kk f')⁻¹ * (C.theta (D f'))⁻¹
              = C.theta (D f) * ((c ^ Kk f * (c ^ Kk f')⁻¹) * (C.theta (D f'))⁻¹) := by group
            _ = C.theta (D f) * ((C.theta (D f'))⁻¹ * (c ^ Kk f * (c ^ Kk f')⁻¹)) := by rw [h3]
            _ = _ := by group
  have h1 := Nat.card_le_card_of_injective g hinj
  have h2 := card_rootsOfUnity K 3
  omega

end Blocks

end CFSG.RankThree.PartTwo.Sec21.Item21Res11Proof
