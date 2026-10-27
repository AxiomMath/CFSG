module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Blocks
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4OddSimple
public import CFSG.RankThree.PartOne.KF.R7Levi

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.RankThree.PartOne.KFU (diagU diagU_val diagU_injective diagUHom diagU_one diagU_pow
  diagU_apply_same torusVec torusSU mem_torusSU_iff apply_eq_zero_of_commute_diagU)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (blk2 blkGL2 coe_blkGL2 blkSU2 dvecD0)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3 (blk2L blkGL2L coe_blkGL2L blkSU2L dvecC centC
  blockUp blockLow ker_blockLow ker_blockUp)

variable {L : Type} [Field L]

theorem entry_eq_one_of_perfect {n : ℕ} {v : Fin n → Lˣ} {l : Fin n}
    (hl : ∀ j, j ≠ l → v l ≠ v j) {K : Subgroup (GL (Fin n) L)}
    (hKC : K ≤ Subgroup.centralizer {diagU v}) (hKp : ⁅K, K⁆ = K) {k : GL (Fin n) L}
    (hk : k ∈ K) : (k : Matrix (Fin n) (Fin n) L) l l = 1 := by
  classical
  set C := Subgroup.centralizer ({diagU v} : Set (GL (Fin n) L)) with hC
  have hrow : ∀ g ∈ C, ∀ j, j ≠ l → (g : Matrix (Fin n) (Fin n) L) l j = 0 := fun g hg j hj =>
    apply_eq_zero_of_commute_diagU (Subgroup.mem_centralizer_singleton_iff.mp hg) (hl j hj)
  let χ : C →* L :=
    { toFun := fun g => ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) l l
      map_one' := by simp
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
        rw [Finset.sum_eq_single l (fun j _ hj => by rw [hrow g g.2 j hj, zero_mul])
          (fun h' => absurd (Finset.mem_univ l) h')] }
  have hcomm : ⁅C, C⁆ ≤ χ.toHomUnits.ker.map C.subtype := by
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    refine ⟨⁅(⟨g, hg⟩ : C), ⟨g', hg'⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hk' : k ∈ ⁅C, C⁆ := Subgroup.commutator_mono hKC hKC (by rw [hKp]; exact hk)
  obtain ⟨g, hg, rfl⟩ := hcomm hk'
  have h1 := congrArg Units.val (MonoidHom.mem_ker.mp hg)
  simpa [χ] using h1

theorem pow_three_of_mem_torusSU {n : ℕ} {z : GL (Fin n) L} (hz : z ∈ torusSU 3 n L) :
    z ^ 3 = 1 := by
  obtain ⟨d, hd3, -, rfl⟩ := mem_torusSU_iff.mp hz
  rw [diagU_pow]
  have : d ^ 3 = 1 := funext fun i => by simp [hd3 i]
  rw [this, diagU_one]

theorem mem_torusVec_of_diagU_mem {n : ℕ} {d : Fin n → Lˣ} (hd : diagU d ∈ torusSU 3 n L) :
    d ∈ torusVec 3 n L := by
  obtain ⟨d', hd'3, hd'p, hd'⟩ := mem_torusSU_iff.mp hd
  obtain rfl := diagU_injective hd'
  exact ⟨hd'3, hd'p⟩

theorem mem_ker_evalMonoidHom {d : Fin 4 → Lˣ} {i : Fin 4} :
    d ∈ (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) i).ker ↔ d i = 1 :=
  MonoidHom.mem_ker

theorem card_torusVec_kerEval_le [Finite L] :
    Nat.card ↥(torusVec 3 4 L ⊓ (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 3).ker) ≤ 9 := by
  set T := torusVec 3 4 L ⊓ (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 3).ker with hT
  have hmem : ∀ d ∈ T, (∀ i, d i ^ 3 = 1) ∧ ∏ i, d i = 1 ∧ d 3 = 1 := by
    intro d hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := Subgroup.mem_inf.mp hd
    exact ⟨h1, h2, mem_ker_evalMonoidHom.mp h3⟩
  let φ : T → rootsOfUnity 3 L × rootsOfUnity 3 L := fun d =>
    (⟨d.1 0, (mem_rootsOfUnity 3 _).mpr ((hmem d.1 d.2).1 0)⟩,
      ⟨d.1 1, (mem_rootsOfUnity 3 _).mpr ((hmem d.1 d.2).1 1)⟩)
  have hφ : Function.Injective φ := by
    intro d e hde
    have h0 : d.1 0 = e.1 0 := congrArg (fun x => ((x.1 : rootsOfUnity 3 L) : Lˣ)) hde
    have h1 : d.1 1 = e.1 1 := congrArg (fun x => ((x.2 : rootsOfUnity 3 L) : Lˣ)) hde
    obtain ⟨-, hdp, hd3⟩ := hmem d.1 d.2
    obtain ⟨-, hep, he3⟩ := hmem e.1 e.2
    rw [Fin.prod_univ_four, hd3, mul_one] at hdp
    rw [Fin.prod_univ_four, he3, mul_one, ← h0, ← h1] at hep
    have h2 : d.1 2 = e.1 2 := mul_left_cancel (hdp.trans hep.symm)
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact hd3.trans he3.symm
  calc Nat.card T ≤ Nat.card (rootsOfUnity 3 L × rootsOfUnity 3 L) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 3 L) * Nat.card (rootsOfUnity 3 L) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity L 3) (card_rootsOfUnity L 3)

theorem card_torusVec_kerEval₂_le [Finite L] :
    Nat.card ↥(torusVec 3 4 L ⊓ (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 2).ker ⊓
      (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 3).ker) ≤ 3 := by
  set T := torusVec 3 4 L ⊓ (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 2).ker ⊓
    (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 3).ker with hT
  have hmem : ∀ d ∈ T, (∀ i, d i ^ 3 = 1) ∧ ∏ i, d i = 1 ∧ d 2 = 1 ∧ d 3 = 1 := by
    intro d hd
    obtain ⟨hd', h3⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨⟨h1, h2⟩, h2'⟩ := Subgroup.mem_inf.mp hd'
    exact ⟨h1, h2, mem_ker_evalMonoidHom.mp h2', mem_ker_evalMonoidHom.mp h3⟩
  let φ : T → rootsOfUnity 3 L := fun d =>
    ⟨d.1 0, (mem_rootsOfUnity 3 _).mpr ((hmem d.1 d.2).1 0)⟩
  have hφ : Function.Injective φ := by
    intro d e hde
    have h0 : d.1 0 = e.1 0 := congrArg (fun x : rootsOfUnity 3 L => (x : Lˣ)) hde
    obtain ⟨-, hdp, hd2, hd3⟩ := hmem d.1 d.2
    obtain ⟨-, hep, he2, he3⟩ := hmem e.1 e.2
    rw [Fin.prod_univ_four, hd2, hd3, mul_one, mul_one] at hdp
    rw [Fin.prod_univ_four, he2, he3, mul_one, mul_one, ← h0] at hep
    have h1 : d.1 1 = e.1 1 := mul_left_cancel (hdp.trans hep.symm)
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact hd2.trans he2.symm
    · exact hd3.trans he3.symm
  exact (Nat.card_le_card_of_injective φ hφ).trans (card_rootsOfUnity L 3)

theorem falseA [Finite L] {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {K E : Subgroup (GL (Fin 4) L)}
    (hKC : K ≤ Subgroup.centralizer {diagU ![ω, ω, ω, 1]}) (hKp : ⁅K, K⁆ = K) (hEK : E ≤ K)
    (hE9 : Nat.card E = 9) (hET : E ≤ torusSU 3 4 L)
    (hEZ : ∀ z ∈ E, (∀ k ∈ K, z * k = k * z) → z = 1) : False := by
  have hl : ∀ j : Fin 4, j ≠ 3 → (![ω, ω, ω, 1] : Fin 4 → Lˣ) 3 ≠ ![ω, ω, ω, 1] j := by
    intro j hj
    fin_cases j
    · simpa using (Ne.symm hω1)
    · simpa using (Ne.symm hω1)
    · simpa using (Ne.symm hω1)
    · exact absurd rfl hj
  set T := torusVec 3 4 L ⊓ (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 3).ker with hT
  have hET' : E ≤ T.map diagUHom := by
    intro z hz
    obtain ⟨d, hd3, hdp, rfl⟩ := mem_torusSU_iff.mp (hET hz)
    refine ⟨d, Subgroup.mem_inf.mpr ⟨⟨hd3, hdp⟩, mem_ker_evalMonoidHom.mpr ?_⟩, rfl⟩
    have h33 := entry_eq_one_of_perfect hl hKC hKp (hEK hz)
    rw [diagU_apply_same] at h33
    exact Units.ext h33
  have hTE : E = T.map diagUHom := Subgroup.eq_of_le_of_card_ge hET' (by
    rw [Subgroup.card_map_of_injective diagU_injective, hE9]
    exact card_torusVec_kerEval_le)
  have hDE : diagU ![ω, ω, ω, 1] ∈ E := by
    rw [hTE]
    refine ⟨![ω, ω, ω, 1], Subgroup.mem_inf.mpr ⟨⟨fun i => ?_, ?_⟩,
      mem_ker_evalMonoidHom.mpr rfl⟩, rfl⟩
    · fin_cases i <;> simp [hω3]
    · rw [Fin.prod_univ_four]
      change ω * ω * ω * 1 = 1
      rw [mul_one, ← pow_three', hω3]
  have h1 := hEZ _ hDE (fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm)
  apply hω1
  have h00 := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L) 0 0) h1
  simp only [diagU_apply_same, Units.val_one, Matrix.one_apply_eq] at h00
  exact Units.ext h00

theorem falseB [Finite L] {ω : Lˣ} (hω1 : ω ≠ 1) (hω2 : ω ≠ ω⁻¹) {K E : Subgroup (GL (Fin 4) L)}
    (hKC : K ≤ Subgroup.centralizer {diagU (dvecD0 ω)}) (hKp : ⁅K, K⁆ = K) (hEK : E ≤ K)
    (hE9 : Nat.card E = 9) (hET : E ≤ torusSU 3 4 L) : False := by
  have hω1' : ω⁻¹ ≠ 1 := fun h => hω1 (inv_eq_one.mp h)
  have hl2 : ∀ j : Fin 4, j ≠ 2 → dvecD0 ω 2 ≠ dvecD0 ω j := by
    intro j hj
    fin_cases j
    · simpa [dvecD0] using hω1
    · simpa [dvecD0] using hω1
    · exact absurd rfl hj
    · simpa [dvecD0] using hω2
  have hl3 : ∀ j : Fin 4, j ≠ 3 → dvecD0 ω 3 ≠ dvecD0 ω j := by
    intro j hj
    fin_cases j
    · simpa [dvecD0] using hω1'
    · simpa [dvecD0] using hω1'
    · simpa [dvecD0] using hω2.symm
    · exact absurd rfl hj
  set T := torusVec 3 4 L ⊓ (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 2).ker ⊓
    (Pi.evalMonoidHom (fun _ : Fin 4 => Lˣ) 3).ker with hT
  have hET' : E ≤ T.map diagUHom := by
    intro z hz
    obtain ⟨d, hd3, hdp, rfl⟩ := mem_torusSU_iff.mp (hET hz)
    have h22 := entry_eq_one_of_perfect hl2 hKC hKp (hEK hz)
    have h33 := entry_eq_one_of_perfect hl3 hKC hKp (hEK hz)
    rw [diagU_apply_same] at h22 h33
    exact ⟨d, Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨⟨hd3, hdp⟩,
      mem_ker_evalMonoidHom.mpr (Units.ext h22)⟩, mem_ker_evalMonoidHom.mpr (Units.ext h33)⟩, rfl⟩
  have hle := Subgroup.card_le_of_le hET'
  rw [Subgroup.card_map_of_injective diagU_injective, hE9] at hle
  have : Nat.card T ≤ 3 := card_torusVec_kerEval₂_le
  omega

theorem blk2_mul_blk2L_comm (X Y : Matrix (Fin 2) (Fin 2) L) :
    blk2 X * blk2L Y = blk2L Y * blk2 X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2, blk2L, Matrix.mul_apply, Fin.sum_univ_four]

theorem falseC [Finite L] {f : ℕ} (h : UnitaryFieldData 2 f L) {ω : Lˣ} (hω : ω ≠ ω⁻¹)
    {K E : Subgroup (GL (Fin 4) L)} (hKC : K ≤ centC f L ω) (hKp : ⁅K, K⁆ = K) (hEK : E ≤ K)
    (hE9 : Nat.card E = 9) (hET : E ≤ torusSU 3 4 L) (hN : NoCommNormalPair3 K) : False := by
  classical
  set C := centC f L ω with hCdef
  let χ : C →* Lˣ := ((Matrix.detMonoidHom).comp (blockUp (f := f) hω)).toHomUnits
  have hcomm : ⁅C, C⁆ ≤ χ.ker.map C.subtype := by
    rw [Subgroup.commutator_le]
    intro g hg g' hg'
    refine ⟨⁅(⟨g, hg⟩ : C), ⟨g', hg'⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hdetK : ∀ k (hk : k ∈ K), (blockUp (f := f) hω ⟨k, hKC hk⟩).det = 1 := by
    intro k hk
    have hk' : k ∈ ⁅C, C⁆ := Subgroup.commutator_mono hKC hKC (by rw [hKp]; exact hk)
    obtain ⟨g, hg, hgk⟩ := hcomm hk'
    have h1 := congrArg Units.val (MonoidHom.mem_ker.mp hg)
    have hg' : g = ⟨k, hKC hk⟩ := Subtype.ext hgk
    subst hg'
    simpa [χ] using h1
  have hup : ∀ (d : Fin 4 → Lˣ) (hd : diagU d ∈ C),
      blockUp (f := f) hω ⟨diagU d, hd⟩ = !![(d 0 : L), 0; 0, (d 1 : L)] := by
    intro d hd
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockUp, diagU_val]
  have hlow : ∀ (d : Fin 4 → Lˣ) (hd : diagU d ∈ C),
      blockLow (f := f) hω ⟨diagU d, hd⟩ = !![(d 2 : L), 0; 0, (d 3 : L)] := by
    intro d hd
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockLow, diagU_val]
  have hE01 : ∀ d, diagU d ∈ E → d 0 * d 1 = 1 := by
    intro d hd
    have h1 := hdetK _ (hEK hd)
    rw [hup, Matrix.det_fin_two_of] at h1
    simp only [mul_zero, sub_zero] at h1
    exact Units.ext (by simpa using h1)
  set E₀ : Subgroup (Fin 4 → Lˣ) := E.comap diagUHom with hE₀
  have hE₀map : E₀.map diagUHom = E :=
    Subgroup.map_comap_eq_self (hET.trans (Subgroup.map_le_range diagUHom (torusVec 3 4 L)))
  have hE₀9 : Nat.card E₀ = 9 := by
    rw [← hE9, ← hE₀map, Subgroup.card_map_of_injective diagU_injective]
  have hE₀T : ∀ d ∈ E₀, d ∈ torusVec 3 4 L := fun d hd => mem_torusVec_of_diagU_mem (hET hd)
  have hex : ∀ i : Fin 4, ∃ d ∈ E₀, d ≠ 1 ∧ d i = 1 := by
    intro i
    let φ : E₀ → rootsOfUnity 3 L := fun d =>
      ⟨d.1 i, (mem_rootsOfUnity 3 _).mpr ((hE₀T d.1 d.2).1 i)⟩
    have hni : ¬ Function.Injective φ := fun hinj => by
      have h1 := Nat.card_le_card_of_injective φ hinj
      have h2 := card_rootsOfUnity L 3
      omega
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hni
    refine ⟨a.1 * b.1⁻¹, mul_mem a.2 (inv_mem b.2), fun h1 => hne (Subtype.ext
      (mul_inv_eq_one.mp h1)), ?_⟩
    have : a.1 i = b.1 i := congrArg (fun x : rootsOfUnity 3 L => (x : Lˣ)) hab
    simp [this]
  set N₁ : Subgroup K := ((blockLow (f := f) hω).comp (Subgroup.inclusion hKC)).ker with hN₁
  set N₂ : Subgroup K := ((blockUp (f := f) hω).comp (Subgroup.inclusion hKC)).ker with hN₂
  have hN₁mem : ∀ a ∈ N₁, ((a : K) : GL (Fin 4) L) ∈ blkSU2 f L := by
    intro a ha
    have ha' : Subgroup.inclusion hKC a ∈ (blockLow (f := f) hω).ker := ha
    rw [ker_blockLow h hω, Subgroup.mem_subgroupOf] at ha'
    exact ha'
  have hN₂mem : ∀ b ∈ N₂, ((b : K) : GL (Fin 4) L) ∈ blkSU2L f L := by
    intro b hb
    have hb' : Subgroup.inclusion hKC b ∈ (blockUp (f := f) hω).ker := hb
    rw [ker_blockUp h hω, Subgroup.mem_subgroupOf] at hb'
    exact hb'
  have hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨X, -, hX⟩ := hN₁mem a ha
    obtain ⟨Y, -, hY⟩ := hN₂mem b hb
    apply Subtype.ext
    change (a : GL (Fin 4) L) * b = b * a
    rw [← hX, ← hY]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_blkGL2, coe_blkGL2L]
    exact blk2_mul_blk2L_comm _ _
  obtain ⟨d, hdE, hd1, hd2⟩ := hex 2
  obtain ⟨d', hd'E, hd'1, hd'0⟩ := hex 0
  have hdE' : diagU d ∈ E := hdE
  have hd'E' : diagU d' ∈ E := hd'E
  have hd3 : d 3 = 1 := by
    have hp := (hE₀T d hdE).2
    rw [Fin.prod_univ_four, hE01 d hdE', one_mul, hd2, one_mul] at hp
    exact hp
  have hd'1' : d' 1 = 1 := by
    have h01 := hE01 d' hd'E'
    rwa [hd'0, one_mul] at h01
  set a : K := ⟨diagU d, hEK hdE'⟩ with ha
  set b : K := ⟨diagU d', hEK hd'E'⟩ with hb
  have haN : a ∈ N₁ := by
    rw [hN₁, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have : Subgroup.inclusion hKC a = ⟨diagU d, hKC (hEK hdE')⟩ := rfl
    rw [this, hlow, hd2, hd3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hbN : b ∈ N₂ := by
    rw [hN₂, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have : Subgroup.inclusion hKC b = ⟨diagU d', hKC (hEK hd'E')⟩ := rfl
    rw [this, hup, hd'0, hd'1']
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hne : ∀ {e : Fin 4 → Lˣ} (he : diagU e ∈ K), e ≠ 1 → (⟨diagU e, he⟩ : K) ≠ 1 := by
    intro e he he1 h1
    apply he1
    apply diagU_injective
    rw [diagU_one]
    exact congrArg Subtype.val h1
  have hpow : ∀ {e : Fin 4 → Lˣ} (he : diagU e ∈ E), (⟨diagU e, hEK he⟩ : K) ^ 3 = 1 := by
    intro e he
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_three_of_mem_torusSU (hET he)
  exact hN N₁ N₂ (MonoidHom.normal_ker _) (MonoidHom.normal_ker _) hc a haN (hne _ hd1)
    (hpow hdE') b hbN (hne _ hd'1) (hpow hd'E')

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
