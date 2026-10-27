module

public import CFSG.Quasithin.Background.RonanH155Alt3Data
public import CFSG.Quasithin.Background.RonanH155Abs
public import CFSG.Quasithin.Background.RonanH155Rest
public import CFSG.Quasithin.Background.RonanH155Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk CFSG.QuasithinUnique.Setup.X1
  CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH154

theorem W10_sq (v : W10) : v * v = 1 := by
  obtain ⟨m, -, rfl⟩ := toW_surj 10 v
  rw [← toW_xor, Nat.xor_self, toW_zero]

theorem hasArr_powA24 {σ : P24} {a : Array ℕ} (h : HasArr σ a) :
    ∀ n : ℕ, HasArr (σ ^ n) (powA24 a n)
  | 0 => by
    rw [pow_zero]
    exact hasArr_idA24
  | n + 1 => by
    rw [pow_succ']
    exact hasArr_compA24 h (hasArr_powA24 h n)

theorem commute_of_arrs {g i : P24} {gA iA : Array ℕ} (hg : HasArr g gA) (hi : HasArr i iA)
    (h : compA24 gA iA = compA24 iA gA) : g * i = i * g := by
  have h2 : HasArr (i * g) (compA24 gA iA) := by
    rw [h]
    exact hasArr_compA24 hi hg
  exact eq_of_hasArr (hasArr_compA24 hg hi) h2

theorem normalizes_of_arrs {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s)
    {g : P24} {gA gI : Array ℕ} (hg : HasArr g gA) (hgi : HasArr g⁻¹ gI)
    (h1 : ∀ s ∈ subprods l, ∃ s' ∈ subprods l, compA24 (compA24 gA (arrP2 s)) gI = arrP2 s')
    (h2 : ∀ s ∈ subprods l, ∃ s' ∈ subprods l, compA24 (compA24 gI (arrP2 s)) gA = arrP2 s') :
    ∀ x : P24, x ∈ A ↔ g * x * g⁻¹ ∈ A := by
  have key : ∀ (u : P24) (uA uI : Array ℕ), HasArr u uA → HasArr u⁻¹ uI →
      (∀ s ∈ subprods l, ∃ s' ∈ subprods l, compA24 (compA24 uA (arrP2 s)) uI = arrP2 s') →
      ∀ x ∈ A, u * x * u⁻¹ ∈ A := by
    intro u uA uI hu hui hh x hx
    obtain ⟨s, hs, rfl⟩ := (hAeq x).1 hx
    obtain ⟨s', hs', hs'e⟩ := hh s hs
    have harr : HasArr (u * PG2.toPerm s * u⁻¹) (compA24 (compA24 uA (arrP2 s)) uI) :=
      hasArr_compA24 (hasArr_compA24 hu (hasArr_toPerm s)) hui
    rw [hs'e] at harr
    have : u * PG2.toPerm s * u⁻¹ = PG2.toPerm s' := eq_of_hasArr harr (hasArr_toPerm s')
    rw [this]
    exact (hAeq _).2 ⟨s', hs', rfl⟩
  intro x
  constructor
  · exact key g gA gI hg hgi h1 x
  · intro hx
    have h := key g⁻¹ gI gA hgi (by rw [inv_inv]; exact hg) h2 _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h
    exact h

theorem smul_fixedSetR_of_comm {i x : P24} (h : x * i = i * x) :
    x • fixedSetR i = fixedSetR i := by
  have hfix : ∀ y : Fin 24, y ∈ fixedSetR i ↔ i y = y := fun y => by simp [fixedSetR]
  have hc : ∀ y, x (i y) = i (x y) := fun y => congrArg (fun f : P24 => f y) h
  ext y
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hfix] at hz ⊢
    rw [Equiv.Perm.smul_def, ← hc, hz]
  · intro hy
    rw [hfix] at hy
    refine ⟨x⁻¹ y, ?_, by simp⟩
    rw [hfix]
    apply x.injective
    have hxy : x (x⁻¹ y) = y := by simp
    rw [hc, hxy, hy]

theorem fixedSetR_eq_maskSet {d : Alt3Data} (hok : Alt3OK d) :
    fixedSetR (PG2.toPerm d.si) = maskSet d.mO := by
  obtain ⟨-, -, -, -, hfixset, -⟩ := hok
  ext p
  have h1 : p ∈ fixedSetR (PG2.toPerm d.si) ↔ PG2.toPerm d.si p = p := by simp [fixedSetR]
  rw [h1, ← hfixset p, ← (hasArr_toPerm d.si p)]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Fin.ext h

theorem card_C_le {d : Alt3Data} (hok : Alt3OK d) :
    Nat.card ↥(mog22plus ⊓ Subgroup.centralizer ({PG2.toPerm d.si} : Set P24)) ≤ 2688 := by
  have hfx := fixedSetR_eq_maskSet hok
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hbfs, hnd, hlt, hlen, -⟩ := hok
  have hle : mog22plus ⊓ Subgroup.centralizer ({PG2.toPerm d.si} : Set P24) ≤
      MY mog22plus (maskSet d.mO) := by
    intro x hx
    have hcomm := Subgroup.mem_centralizer_iff.1 hx.2 (PG2.toPerm d.si) rfl
    refine ⟨hx.1, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [← hfx]
    exact smul_fixedSetR_of_comm hcomm.symm
  have h3 := card_stab_plus_mul_le hbfs hnd hlt
  rw [hlen] at h3
  calc Nat.card ↥(mog22plus ⊓ Subgroup.centralizer ({PG2.toPerm d.si} : Set P24))
      ≤ Nat.card ↥(MY mog22plus (maskSet d.mO)) := Subgroup.card_le_of_le hle
    _ = Nat.card (MulAction.stabilizer ↥mog22plus (maskSet d.mO)) :=
        card_inf_stabilizer_eq (Γ := mog22plus) _
    _ ≤ 2688 := by omega

theorem toW_mem_fixV_of_fixMasks {A : Subgroup P24} {l : List PG2}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods l, x = PG2.toPerm s) {m : ℕ}
    (hm : m ∈ fixMasks 10 actP2 l) : toW 10 m ∈ fixV (rImg Rc A) := by
  obtain ⟨-, hfix⟩ := mem_fixMasks.1 hm
  rw [mem_fixV_iff_chain (isChainSub_rImg hAeq)]
  intro s hs
  exact (autP2_toW s m).trans (congrArg (toW 10) (hfix s hs))

theorem restrict_ne_one {N : Subgroup P24} (hNΓ : N ≤ mog22plus) (W : Subgroup W10)
    (hinv : ∀ g : ↥N, ∀ w ∈ W, (Rc.comp (Subgroup.inclusion hNΓ)) g w ∈ W) (g : ↥N)
    {a : Array ℕ} (ha : HasArr (g : P24) a) {m : ℕ} (hmW : toW 10 m ∈ W) (hm : m < 2 ^ 10)
    (hne : act10 a m ≠ m) : restrictAutHom (Rc.comp (Subgroup.inclusion hNΓ)) W hinv g ≠ 1 := by
  intro h
  have h1 : ((restrictAutHom (Rc.comp (Subgroup.inclusion hNΓ)) W hinv g ⟨toW 10 m, hmW⟩ : ↥W) :
      W10) = toW 10 m := by
    rw [h]
    rfl
  have h1' : Rc (Subgroup.inclusion hNΓ g) (toW 10 m) = toW 10 m := h1
  have h2 : Rc (Subgroup.inclusion hNΓ g) (toW 10 m) = toW 10 (act10 a m) := Rc_toW _ ha m
  exact hne (toW_inj (act10_lt _ _) hm (h2.symm.trans h1'))

theorem alt3_of_data
    (d : Alt3Data) (hok : Alt3OK d) {A : Subgroup P24}
    (hAeq : ∀ x : P24, x ∈ A ↔ ∃ s ∈ subprods d.l, x = PG2.toPerm s)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hcard : Nat.card A = 16) :
    Alt3Struct mog22plus A 0 1 ∧ CFSG.Quasithin.rk ↥(fixV (rImg Rc A)) = 3 ∧
      xiV (rImg Rc A) = ⊤ := by
  have hCle := card_C_le hok
  have hfx := fixedSetR_eq_maskSet hok
  obtain ⟨hsi, hi0, hocard, hosyn, hfixset, h0nin, ⟨hhinv, hhok, hh0, hh1, hhcomm, hhn1, hhn2⟩,
    hh7, hmh, hmhne, ⟨hyinv, hyok, hy0, hy1, hycomm, hyn1, hyn2⟩, hy2, hmy, hmyne, hbfs, hnd, hlt,
    hlen, hfix, hw, hwl⟩ := hok
  have hrk : CFSG.Quasithin.rk ↥(fixV (rImg Rc A)) = 3 := rk_fixV_chain hAeq hfix
  have hxi : xiV (rImg Rc A) = ⊤ := xi_top_wit hAeq hw hwl
  refine ⟨?_, hrk, hxi⟩
  set i : P24 := PG2.toPerm d.si with hi
  have hiA : i ∈ A := (hAeq _).2 ⟨d.si, hsi, rfl⟩
  have hi01 : i 0 = 1 := (hasArr_toPerm d.si).apply_eq 0 hi0
  have hiM : i ∉ M22g 0 1 := by
    intro hmem
    have h0 : i • (0 : Fin 24) = 0 := MulAction.mem_stabilizer_iff.1 hmem.1.2
    rw [Equiv.Perm.smul_def, hi01] at h0
    exact absurd h0 (by decide)
  have hoct : IsOctR (maskSet d.mO) := sextStd_isOct_maskSet hocard hosyn
  have hnot : ¬ ((0 : Fin 24) ∈ maskSet d.mO ∧ (1 : Fin 24) ∈ maskSet d.mO) := fun h => h0nin h.1
  set hP : P24 := permOfArr 24 d.hA d.hI hhinv with hhP
  have hhArr : HasArr hP d.hA := hasArr_permOfArr hhinv
  have hhArrI : HasArr hP⁻¹ d.hI := hasArr_permOfArr_inv hhinv
  have hhΓ : hP ∈ mog22plus := permOfArr_mem_mog22plus hhinv hhok hh0 hh1
  have hhC : hP ∈ Subgroup.centralizer ({i} : Set P24) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact (commute_of_arrs hhArr (hasArr_toPerm d.si) hhcomm).symm
  have hhN : hP ∈ Subgroup.normalizer (A : Set P24) :=
    Subgroup.mem_normalizer_iff.2 (normalizes_of_arrs hAeq hhArr hhArrI hhn1 hhn2)
  set yP : P24 := permOfArr 24 d.yA d.yI hyinv with hyP
  have hyArr : HasArr yP d.yA := hasArr_permOfArr hyinv
  have hyArrI : HasArr yP⁻¹ d.yI := hasArr_permOfArr_inv hyinv
  have hyΓ : yP ∈ mog22plus := permOfArr_mem_mog22plus hyinv hyok hy0 hy1
  have hyC : yP ∈ Subgroup.centralizer ({i} : Set P24) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact (commute_of_arrs hyArr (hasArr_toPerm d.si) hycomm).symm
  have hyN : yP ∈ Subgroup.normalizer (A : Set P24) :=
    Subgroup.mem_normalizer_iff.2 (normalizes_of_arrs hAeq hyArr hyArrI hyn1 hyn2)
  have hP7 : hP ^ 7 = 1 := by
    have h : HasArr (hP ^ 7) idA24 := by
      rw [← hh7]
      exact hasArr_powA24 hhArr 7
    exact eq_of_hasArr h hasArr_idA24
  have hy2' : yP ^ 2 = 1 := by
    have h : HasArr (yP ^ 2) idA24 := by
      rw [← hy2, pow_two]
      exact hasArr_compA24 hyArr hyArr
    exact eq_of_hasArr h hasArr_idA24
  set C : Subgroup P24 := mog22plus ⊓ Subgroup.centralizer ({i} : Set P24) with hC
  set N : Subgroup P24 := C ⊓ Subgroup.normalizer (A : Set P24) with hN
  have hNΓ : N ≤ mog22plus := fun x hx => hx.1.1
  have hNC : N ≤ C := inf_le_left
  have hAN : A ≤ N := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := (hAeq a).1 ha
    have haΓ : PG2.toPerm s ∈ mog22plus := P2_le_mog22plus_sylw (PG2.toPerm_mem_P2 s)
    refine ⟨⟨haΓ, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩, Subgroup.le_normalizer ha⟩
    rw [Set.mem_singleton_iff.1 hg]
    exact hcomm i hiA _ ha
  set W : Subgroup W10 := fixV (rImg Rc A) with hW
  have hinv : ∀ g : ↥N, ∀ w ∈ W, (Rc.comp (Subgroup.inclusion hNΓ)) g w ∈ W := by
    intro g w hw
    exact fixV_rImg_invariant Rc A (Subgroup.inclusion hNΓ g)
      (Subgroup.mem_normalizer_iff.1 g.2.2) w hw
  set ψ : ↥N →* MulAut ↥W := restrictAutHom (Rc.comp (Subgroup.inclusion hNΓ)) W hinv with hψ
  have hWcard : Nat.card ↥W = 8 := by
    have h := card_fixV chainAct_P2 (isChainSub_rImg hAeq)
    rw [hfix] at h
    exact h.trans (by norm_num)
  have hWsq : ∀ w : ↥W, w * w = 1 := fun w => Subtype.ext (W10_sq (w : W10))
  have hψA : ∀ a : ↥N, (a : P24) ∈ A → ψ a = 1 := by
    intro a ha
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    show Rc (Subgroup.inclusion hNΓ a) (w : W10) = (w : W10)
    exact mem_fixV.1 w.2 _
      (Subgroup.mem_map_of_mem Rc (Subgroup.mem_subgroupOf.2 ha))
  have hhmemN : hP ∈ N := ⟨⟨hhΓ, hhC⟩, hhN⟩
  have hymemN : yP ∈ N := ⟨⟨hyΓ, hyC⟩, hyN⟩
  have h7 : ∃ h : ↥N, ψ h ^ 7 = 1 ∧ ψ h ≠ 1 := by
    refine ⟨⟨hP, hhmemN⟩, ?_, ?_⟩
    · have h1 : (⟨hP, hhmemN⟩ : ↥N) ^ 7 = 1 := Subtype.ext hP7
      rw [← map_pow, h1, map_one]
    · exact restrict_ne_one hNΓ W hinv ⟨hP, hhmemN⟩ hhArr
        (toW_mem_fixV_of_fixMasks hAeq hmh) (mem_fixMasks.1 hmh).1 hmhne
  have h2 : ∃ y : ↥N, ψ y ^ 2 = 1 ∧ ψ y ≠ 1 := by
    refine ⟨⟨yP, hymemN⟩, ?_, ?_⟩
    · have h1 : (⟨yP, hymemN⟩ : ↥N) ^ 2 = 1 := Subtype.ext hy2'
      rw [← map_pow, h1, map_one]
    · exact restrict_ne_one hNΓ W hinv ⟨yP, hymemN⟩ hyArr
        (toW_mem_fixV_of_fixMasks hAeq hmy) (mem_fixMasks.1 hmy).1 hmyne
  obtain ⟨hpc, π, hsurj, hker⟩ :=
    alt3_abstract hWcard hWsq A N C hAN hNC hcard hCle ψ hψA h7 h2
  exact ⟨i, hiA, hiM, ⟨maskSet d.mO, hoct, hnot, hfx⟩, hpc.symm, π, hsurj, hker⟩

end CFSG.Quasithin.RonanH155
