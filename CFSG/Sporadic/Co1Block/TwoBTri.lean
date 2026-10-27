module

public import CFSG.Sporadic.Co1Block.TwoBTriBase1

public import CFSG.Sporadic.Co1Block.TwoBCent
public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs
public meta import CFSG.Sporadic.Co1Block.ConjBData
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Certificate10070
public import CFSG.Sporadic.Co1.Module.TwoBFrameInputs
public import CFSG.Sporadic.Co1Block.TwoBCheck
public import Certificates.Kernel.Co1B.Tri2045

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem twoB_tri_parts :
    Native.trisOK twoBTris CFSG.Sporadic.Co1Schreier.Native.aR = true ∧
    Native.tableOK twoBTab twoBTris = true ∧
    (∀ r ∈ twoBBm, Native.triOK twoBTab twoBTris r = true) ∧
    Native.triOK twoBTab twoBTris twoBXYRows.1 = true ∧
    Native.triOK twoBTab twoBTris twoBXYRows.2 = true ∧ twoBStrong.size = 6 ∧
    eqA 1365 twoBStrong[0]! twoBXArr = true ∧ eqA 1365 twoBStrong[1]! twoBYArr = true ∧
    rawChainOK 1365 (twoBStrong.extract 0 2) twoBStrong twoBChainBase.toArray twoBW 4 = true ∧
    rawOrbitSizes 1365 twoBStrong twoBChainBase.toArray = [1365, 1024, 180] ∧
    Native.isPrimeOrderA 1365 twoBXArr 2 = true ∧ Native.isPrimeOrderA 1365 twoBYArr 5 = true ∧
    Native.isPrimeOrderA 1365 (compA 1365 twoBXArr twoBYArr) 13 = true ∧
    ∀ r ∈ twoBBm, isInvA 1365 (Native.triPerm twoBTab twoBTris r)
        (invCand 1365 (Native.triPerm twoBTab twoBTris r)) = true ∧
      siftA 1365 (rawLevels 1365 twoBStrong twoBChainBase.toArray) twoBChainBase.toArray 0
        (conjArr (Native.triPerm twoBTab twoBTris r) twoBXArr) = true ∧
      siftA 1365 (rawLevels 1365 twoBStrong twoBChainBase.toArray) twoBChainBase.toArray 0
        (conjArr (Native.triPerm twoBTab twoBTris r) twoBYArr) = true := by
  have h := twoB_tri_check
  simp only [twoBTriCheckOf, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ :=
    h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    fun r hr => ⟨(h14 r hr).1.1, (h14 r hr).1.2, (h14 r hr).2⟩⟩

theorem twoBTris_length : twoBTris.length = 1365 := by
  have h := twoB_tri_parts.1
  simp only [Native.trisOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem triP_mem {k : ℕ} (hk : k < 1365) : triP k ∈ twoBTris := by
  rw [triP, getElem!_pos twoBTris k (by rw [twoBTris_length]; exact hk)]
  exact List.getElem_mem _

theorem tri_vec_lt
    {k x : ℕ} (hk : k < 1365) (hx : inTriN (triP k) x = true) : x < 2 ^ 24 := by
  have h := twoB_tri_parts.1
  simp only [Native.trisOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  have hmem : x ∈ Native.triVecs twoBTris := by
    rw [Native.triVecs, List.mem_flatMap]
    refine ⟨triP k, triP_mem hk, ?_⟩
    rcases inTriN_iff.1 hx with h | h | h <;> simp [h]
  exact (h.1.2 x hmem).1.1

theorem tab_sound
    {x : ℕ} (hx : x < 2 ^ 24) (hk : twoBTab[x]! < 1365) :
    inTriN (triP twoBTab[x]!) x = true := by
  have h := allLt_spec twoB_tab_check hx
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h (Nat.not_le.2 hk)
  · simpa [triP] using h

theorem tab_tri
    {k x : ℕ} (hk : k < 1365) (hx : inTriN (triP k) x = true) :
    twoBTab[x]! = k := by
  have h := twoB_tri_parts.2.1
  simp only [Native.tableOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  have hmem : (triP k, k) ∈ twoBTris.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    show twoBTris[k]? = some twoBTris[k]!
    rw [getElem!_pos twoBTris k (by rw [twoBTris_length]; exact hk)]
    exact List.getElem?_eq_getElem _
  obtain ⟨⟨h1, h2⟩, h3⟩ := h _ hmem
  rcases inTriN_iff.1 hx with rfl | rfl | rfl
  exacts [h1, h2, h3]

theorem inTri_unique
    {v : Vec24} {k k' : ℕ} (hk : k < 1365) (hk' : k' < 1365) (h : InTri v k)
    (h' : InTri v k') : k = k' := by
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨x', hx', he⟩ := h'
  have hxx : x = x' := toVecD_injective (tri_vec_lt hk hx) (tri_vec_lt hk' hx') he
  rw [← tab_tri hk hx, ← tab_tri hk' hx', hxx]

theorem triPres_of_rep
    {M : CFSG.Sporadic.Co1Schreier.Native.Rows} {g : GL24} (hM : MRep M g)
    (hok : Native.triOK twoBTab twoBTris M = true) {k : ℕ} (hk : k < 1365) :
    twoBTab[CFSG.Sporadic.Co1Schreier.Native.act M (triP k).1]! < 1365 ∧ ∀ v, InTri v k →
      InTri (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v)
        twoBTab[CFSG.Sporadic.Co1Schreier.Native.act M (triP k).1]! := by
  have h := hok
  simp only [Native.triOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h (triP k) (triP_mem hk)
  refine ⟨h1, fun v hv => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hv
  have hx' : twoBTab[CFSG.Sporadic.Co1Schreier.Native.act M x]! =
      twoBTab[CFSG.Sporadic.Co1Schreier.Native.act M (triP k).1]! := by
    rcases inTriN_iff.1 hx with rfl | rfl | rfl
    · rfl
    · exact h2
    · exact h3
  refine ⟨CFSG.Sporadic.Co1Schreier.Native.act M x, ?_, MRep.mulVec hM x⟩
  have h1' : twoBTab[CFSG.Sporadic.Co1Schreier.Native.act M x]! < 1365 := by
    rw [hx']
    exact h1
  rw [← hx']
  exact tab_sound (act_lt M x) h1'

theorem triPres_of_mem
    {g : GL24} (hg : g ∈ GA ⊓ Subgroup.centralizer {A₁}) : TriPres g := by
  rw [← twoBE_eq] at hg
  have hg' : g ∈ (Subgroup.closure {g | g ∈ brayEltsG A₁ twoBD1 twoBBray}).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid_of_finite] at hg'
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨r, hr, hrx⟩ :=
      forall₂_mem_left (rep_brayElts rep_A₁ (centCheck_parts twoB_cent_check).1) hx
    intro k hk
    have h := triPres_of_rep hrx (twoB_tri_parts.2.2.1 r hr) hk
    exact ⟨_, h.1, h.2⟩
  | one => exact triPres_one
  | mul x y _ _ hx hy => exact triPres_mul hx hy

abbrev C₁ : Subgroup GA := Subgroup.centralizer ({a₁} : Set GA)

theorem coe_mem_C₁ (c : C₁) : ((c : GA) : GL24) ∈ GA ⊓ Subgroup.centralizer {A₁} := by
  rw [← coe_a₁]
  exact Subgroup.mem_inf.2 ⟨(c : GA).2, mem_centralizer_GA_iff.1 c.2⟩

theorem exists_tri
    (c : C₁) (k : Fin 1365) : ∃ k' : Fin 1365, ∀ v, InTri v k →
    InTri ((((c : GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) k' := by
  obtain ⟨k', hk', h⟩ := triPres_of_mem (coe_mem_C₁ c) k k.2
  exact ⟨⟨k', hk'⟩, h⟩

@[expose] def triAct
    (c : C₁) (k : Fin 1365) : Fin 1365 := (exists_tri c k).choose

theorem triAct_spec
    (c : C₁) (k : Fin 1365) : ∀ v, InTri v k →
    InTri ((((c : GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) (triAct c k) :=
  (exists_tri c k).choose_spec

theorem triAct_eq
    {c : C₁} {k k' : Fin 1365}
    (h : InTri ((((c : GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ triV k) k') :
    triAct c k = k' :=
  Fin.ext (inTri_unique (triAct c k).2 k'.2 (triAct_spec c k _ (triV_mem k)) h)

@[expose, instance_reducible] def triMulAction :
    MulAction C₁ (Fin 1365) where
  smul := triAct
  one_smul k := triAct_eq (by
    show InTri (((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ triV k) k
    rw [Units.val_one, one_mulVec]
    exact triV_mem k)
  mul_smul g h k := triAct_eq (by
    show InTri (((((g : GA) : GL24) * ((h : GA) : GL24) : GL24) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ triV k) (triAct g (triAct h k))
    rw [mulVec_mul']
    exact triAct_spec g _ _ (triAct_spec h k _ (triV_mem k)))


theorem mem_C₁_of {g : GA} (h : (g : GL24) ∈ Subgroup.centralizer {A₁}) : g ∈ C₁ := by
  rw [mem_centralizer_GA_iff, coe_a₁]
  exact h



attribute [local instance] triMulAction

@[expose] def triHom :
    C₁ →* Equiv.Perm (Fin 1365) := MulAction.toPermHom C₁ (Fin 1365)

abbrev twoBD₂ : List GL24 := strongDagG A₁ twoBD1 twoBBray twoBD2

attribute [local instance] triMulAction

theorem triHom_apply
    (c : C₁) (k : Fin 1365) : triHom c k = triAct c k := rfl

theorem rep_triHom
    {c : C₁} {M : CFSG.Sporadic.Co1Schreier.Native.Rows}
    (hM : MRep M ((c : GA) : GL24)) (hok : Native.triOK twoBTab twoBTris M = true) :
    Rep 1365 (Native.triPerm twoBTab twoBTris M) (triHom c) := by
  intro k
  have h := triPres_of_rep hM hok k.2
  have hk : (k : ℕ) < twoBTris.length := by rw [twoBTris_length]; exact k.2
  rw [triHom_apply, triAct_eq (k' := ⟨_, h.1⟩) (h.2 _ (triV_mem k))]
  simp only [Native.triPerm, List.getElem!_toArray, triP]
  rw [getElem!_pos _ _ (by simpa using hk), List.getElem_map, getElem!_pos twoBTris _ hk]

theorem twoBD₂_mem
    (j : ℕ) : twoBD₂.getD j 1 ∈ GA ⊓ Subgroup.centralizer {A₁} :=
  twoBE_le (getD_mem_of_forall strongDag_mem j)

@[expose] def d₂C (j : ℕ) : C₁ :=
  ⟨⟨twoBD₂.getD j 1, (Subgroup.mem_inf.1 (twoBD₂_mem j)).1⟩,
    mem_C₁_of (Subgroup.mem_inf.1 (twoBD₂_mem j)).2⟩

theorem rep_d₂C
    (j : ℕ) : MRep ((CFSG.Sporadic.Co1Schreier.Native.dag twoBBm twoBD2).1.getD j
    CFSG.Sporadic.Co1Schreier.Native.one) ((d₂C j : GA) : GL24) :=
  getD_rep (rep_strongDag rep_A₁ twoB_cent_check) MRep.one j

theorem rep_x :
    Rep 1365 twoBXArr (triHom (d₂C twoBXY.1)) :=
  rep_triHom (rep_d₂C _) twoB_tri_parts.2.2.2.1

theorem rep_y :
    Rep 1365 twoBYArr (triHom (d₂C twoBXY.2)) :=
  rep_triHom (rep_d₂C _) twoB_tri_parts.2.2.2.2.1

end CFSG.Sporadic.Co1Block
