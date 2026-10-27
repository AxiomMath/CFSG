module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsFrame
public import CFSG.Quasithin.H13.A6Rows1321

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Matrix

namespace CFSG.Quasithin.H13.A6.GR


namespace Row6

@[expose] def crdM : Matrix (Fin 4) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0; 0, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1]

@[expose] def secM : Matrix (Fin 6) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 1, 1, 0, 0; 0, 1, 0, 1; 0, 1, 1, 1; 0, 1, 1, 0]

theorem crd_sec : crdM * secM = 1 := by decide +kernel

theorem sec_even : ∀ y : Fin 4 → ZMod 2, ∑ i, (secM *ᵥ y) i = 0 := by decide +kernel

theorem crd_ker : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 → crdM *ᵥ x = 0 →
    x = 0 ∨ x = fun _ => 1 := by decide +kernel

theorem crd_one : crdM *ᵥ (fun _ : Fin 6 => (1 : ZMod 2)) = 0 := by decide +kernel

theorem sec_crd (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    secM *ᵥ (crdM *ᵥ x) = x ∨ secM *ᵥ (crdM *ᵥ x) = x + fun _ => 1 := by
  have h1 : ∑ i, (secM *ᵥ (crdM *ᵥ x)) i = 0 := sec_even _
  have h2 : crdM *ᵥ (x + secM *ᵥ (crdM *ᵥ x)) = 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, crd_sec, Matrix.one_mulVec]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have h3 : ∑ i, (x + secM *ᵥ (crdM *ᵥ x)) i = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, h1, add_zero]
  have key0 : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  have key1 : ∀ a b : ZMod 2, a + b = 1 → b = a + 1 := by decide
  rcases crd_ker _ h3 h2 with h | h
  · left
    funext i
    exact key0 _ _ (congrFun h i)
  · right
    funext i
    exact key1 _ _ (congrFun h i)


@[expose] def pm (σ : Equiv.Perm (Fin 6)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => if σ⁻¹ i = j then 1 else 0

theorem pm_mulVec (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    pm σ *ᵥ x = fun i => x (σ⁻¹ i) := by
  funext i
  simp [pm, Matrix.mulVec, dotProduct, ite_mul]

@[expose] def mat6 (σ : Equiv.Perm (Fin 6)) : Matrix (Fin 4) (Fin 4) (ZMod 2) := crdM * pm σ * secM

@[expose] def crdHom : ↥(G6.coreMod 6) →* Multiplicative (Fin 4 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (crdM *ᵥ Multiplicative.toAdd x.1)
  map_one' := by simp
  map_mul' := by
    intro x y
    simp [Matrix.mulVec_add, ofAdd_add]

theorem mem_ker6 (x : ↥(G6.coreMod 6)) : x ∈ D6.Ker6 ↔ x.1 = 1 ∨ x.1 = G6.allOnes 6 := by
  rw [D6.Ker6, Subgroup.mem_subgroupOf, Subgroup.mem_inf, B5FinPerm.mem_zpowers_allOnes_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

theorem crdHom_ker : D6.Ker6 ≤ crdHom.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  rcases (mem_ker6 x).mp hx with h | h
  · have : Multiplicative.toAdd x.1 = 0 := by rw [h]; rfl
    simp [crdHom, this]
  · have : Multiplicative.toAdd x.1 = fun _ => 1 := by rw [h]; rfl
    simp [crdHom, this, crd_one]

@[expose] noncomputable def kappaHom : D6.Mod6 →* Multiplicative (Fin 4 → ZMod 2) :=
  QuotientGroup.lift D6.Ker6 crdHom crdHom_ker

theorem kappaHom_mk (x : ↥(G6.coreMod 6)) :
    kappaHom (QuotientGroup.mk x) = Multiplicative.ofAdd (crdM *ᵥ Multiplicative.toAdd x.1) := rfl

theorem kappaHom_bijective : Function.Bijective kappaHom := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [kappaHom_mk] at hq
    have h0 : crdM *ᵥ Multiplicative.toAdd x.1 = 0 := by
      have := congrArg Multiplicative.toAdd hq
      simpa using this
    have hsum : ∑ i, Multiplicative.toAdd x.1 i = 0 := (G6.mem_coreMod).1 x.2
    rw [QuotientGroup.eq_one_iff, mem_ker6]
    rcases crd_ker _ hsum h0 with h | h
    · left
      exact Multiplicative.toAdd.injective (by rw [h]; rfl)
    · right
      exact Multiplicative.toAdd.injective (by rw [h]; rfl)
  · intro y
    refine ⟨QuotientGroup.mk ⟨Multiplicative.ofAdd (secM *ᵥ Multiplicative.toAdd y),
      (G6.mem_coreMod).2 (sec_even _)⟩, ?_⟩
    rw [kappaHom_mk]
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, crd_sec, Matrix.one_mulVec, ofAdd_toAdd]

@[expose] noncomputable def kappa : D6.Mod6 ≃* Multiplicative (Fin 4 → ZMod 2) :=
  MulEquiv.ofBijective kappaHom kappaHom_bijective

theorem pm_one (σ : Equiv.Perm (Fin 6)) : pm σ *ᵥ (fun _ => (1 : ZMod 2)) = fun _ => 1 := by
  rw [pm_mulVec]

theorem pm_sum (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    ∑ i, (pm σ *ᵥ x) i = ∑ i, x i := by
  rw [pm_mulVec]
  exact Equiv.sum_comp σ⁻¹ x

theorem crd_perm (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    crdM *ᵥ (pm σ *ᵥ x) = mat6 σ *ᵥ (crdM *ᵥ x) := by
  unfold mat6
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases sec_crd x hx with h | h
  · rw [h]
  · rw [h, Matrix.mulVec_add, pm_one, Matrix.mulVec_add, crd_one, add_zero]

theorem kappa_aut (σ : Equiv.Perm (Fin 6)) (q : D6.Mod6) :
    Multiplicative.toAdd (kappa (D6.aut6 σ q)) = mat6 σ *ᵥ Multiplicative.toAdd (kappa q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [D6.aut6_apply, D6.act6_mk]
  change crdM *ᵥ Multiplicative.toAdd (G6.permAct 6 σ x.1) =
    mat6 σ *ᵥ (crdM *ᵥ Multiplicative.toAdd x.1)
  have h1 : Multiplicative.toAdd (G6.permAct 6 σ x.1) = pm σ *ᵥ Multiplicative.toAdd x.1 := by
    rw [pm_mulVec]
    rfl
  rw [h1]
  exact crd_perm σ _ ((G6.mem_coreMod).1 x.2)

end Row6


namespace Row6

theorem commutator_range_eq_map {G H : Type} [Group G] [Group H] (f : G →* H) :
    ⁅f.range, f.range⁆ = (commutator G).map f := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  rfl

open Equiv CFSG.Assembly.LowTwoRank in
theorem alt6_data {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}
    (hB4 : B4Hyp G L) (hrow : B42Case6 G L A ∨ BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1) :
    ∃ (e : V ≃* D6.Mod6) (ψ : ↥(alternatingGroup (Fin 6)) →* ↥L), Function.Bijective ψ ∧
      ∀ (γ : ↥(alternatingGroup (Fin 6))) (w : V),
        e (((ψ γ : ↥L) : MulAut V) w) = D6.aut6 γ.1 (e w) := by
  rcases hrow with ⟨-, ⟨π, hπ⟩, -⟩ | hSp
  · have hinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
    obtain ⟨e₀, he₀⟩ := G64.RealizesVia.exists_modEquiv hπ
    let e : V ≃* D6.Mod6 := e₀
    refine ⟨e, π, ⟨hinj, hπ.1⟩, fun γ w => ?_⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e w)
    rw [← hm, D6.aut6_apply, D6.act6_mk]
    exact he₀ γ w m (G6.permAct_mem_coreMod (γ : Perm (Fin 6)) m.2) hm.symm
  · obtain ⟨-, hLJ, -⟩ := FFC.ident_sp4 hB4 hSp
    obtain ⟨π₀, hπ⟩ := asSp4S6 V _ ⊤ ⊥ hSp
    have hinj := G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful (by norm_num)) hπ
    obtain ⟨e₀, he₀⟩ := G64.RealizesVia.exists_modEquiv hπ
    let e : V ≃* D6.Mod6 := e₀
    let π : Perm (Fin 6) →* ↥(ffJ G) := π₀
    let f : Perm (Fin 6) →* MulAut V := (ffJ G).subtype.comp π
    have hrange : f.range = ffJ G := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective π hπ.1, Subgroup.map_top,
        Subgroup.range_subtype]
    have hLA : L = (alternatingGroup (Fin 6)).map f := by
      calc L = ⁅ffJ G, ffJ G⁆ := hLJ
        _ = ⁅f.range, f.range⁆ := by rw [hrange]
        _ = (commutator (Perm (Fin 6))).map f := commutator_range_eq_map f
        _ = (alternatingGroup (Fin 6)).map f := by
          rw [alternatingGroup.commutator_perm_eq (by norm_num : 5 ≤ Nat.card (Fin 6))]
    have hfinj : Function.Injective f := (ffJ G).subtype_injective.comp hinj
    have hmem : ∀ γ : ↥(alternatingGroup (Fin 6)), f γ.1 ∈ L := fun γ => by
      rw [hLA]
      exact ⟨γ.1, γ.2, rfl⟩
    refine ⟨e, (f.comp (alternatingGroup (Fin 6)).subtype).codRestrict L hmem,
      ⟨?_, ?_⟩, fun γ w => ?_⟩
    · intro a b hab
      apply Subtype.ext
      apply hfinj
      exact congrArg (fun l : ↥L => (l : MulAut V)) hab
    · intro l
      have hl : (l : MulAut V) ∈ (alternatingGroup (Fin 6)).map f := by
        rw [← hLA]
        exact l.2
      obtain ⟨γ, hγ, hγl⟩ := hl
      exact ⟨⟨γ, hγ⟩, Subtype.ext hγl⟩
    · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (e w)
      rw [← hm, D6.aut6_apply, D6.act6_mk]
      exact he₀ γ.1 w m (G6.permAct_mem_coreMod (γ.1 : Perm (Fin 6)) m.2) hm.symm

end Row6


namespace Row6

@[expose] def Bf (y z : Fin 4 → ZMod 2) : ZMod 2 := (secM *ᵥ y) ⬝ᵥ (secM *ᵥ z)

@[expose] def MemB (K : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ y z, Bf (K *ᵥ y) (K *ᵥ z) = Bf y z

theorem pm_dot (σ : Equiv.Perm (Fin 6)) (a b : Fin 6 → ZMod 2) :
    (pm σ *ᵥ a) ⬝ᵥ (pm σ *ᵥ b) = a ⬝ᵥ b := by
  rw [pm_mulVec, pm_mulVec]
  exact Equiv.sum_comp σ⁻¹ (fun i => a i * b i)

theorem dot_one_left (x : Fin 6 → ZMod 2) : (fun _ => (1 : ZMod 2)) ⬝ᵥ x = ∑ i, x i := by
  simp [dotProduct]

theorem dot_one_one : (fun _ : Fin 6 => (1 : ZMod 2)) ⬝ᵥ (fun _ => (1 : ZMod 2)) = 0 := by
  decide +kernel

theorem memB_mat6 (σ : Equiv.Perm (Fin 6)) : MemB (mat6 σ) := by
  intro y z
  have key : ∀ y : Fin 4 → ZMod 2, ∃ ε : ZMod 2, secM *ᵥ (mat6 σ *ᵥ y) =
      (pm σ *ᵥ (secM *ᵥ y)) + fun _ => ε := by
    intro y
    have hy : mat6 σ *ᵥ y = crdM *ᵥ (pm σ *ᵥ (secM *ᵥ y)) := by
      unfold mat6
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hs : ∑ i, (pm σ *ᵥ (secM *ᵥ y)) i = 0 := by rw [pm_sum]; exact sec_even y
    rw [hy]
    rcases sec_crd _ hs with h | h
    · exact ⟨0, by rw [h]; ext i; simp⟩
    · exact ⟨1, h⟩
  obtain ⟨ε₁, h1⟩ := key y
  obtain ⟨ε₂, h2⟩ := key z
  unfold Bf
  rw [h1, h2]
  have hy0 : ∑ i, (pm σ *ᵥ (secM *ᵥ y)) i = 0 := by rw [pm_sum]; exact sec_even y
  have hz0 : ∑ i, (pm σ *ᵥ (secM *ᵥ z)) i = 0 := by rw [pm_sum]; exact sec_even z
  set u := pm σ *ᵥ (secM *ᵥ y)
  set u' := pm σ *ᵥ (secM *ᵥ z)
  have hc : ∀ ε : ZMod 2, (fun _ : Fin 6 => ε) = ε • (fun _ : Fin 6 => (1 : ZMod 2)) := by
    intro ε
    funext i
    simp
  rw [hc ε₁, hc ε₂, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_dotProduct, dotProduct_smul]
  have e1 : u ⬝ᵥ (fun _ => (1 : ZMod 2)) = 0 := by rw [dotProduct_comm, dot_one_left, hy0]
  have e2 : (fun _ : Fin 6 => (1 : ZMod 2)) ⬝ᵥ u' = 0 := by rw [dot_one_left, hz0]
  rw [e1, e2, dot_one_one, pm_dot]
  simp

end Row6


namespace Row6

@[expose] def gm6 : List (List ℕ) := [[6, 1, 4, 9], [2, 1, 4, 12]]

@[expose] def gp6 : List (List ℕ × List ℕ) :=
  [([6, 1, 4, 9], [2, 5, 4, 10]), ([2, 1, 4, 12], [2, 1, 4, 12])]

@[expose] def gram6 : List ℕ := [2, 1, 8, 4]

@[expose] def u6 : ℕ := 8

@[expose] def words6 : List (List ℕ) := [[], [0], [1], [0, 0]]

@[expose] def binv6 : List ℕ := [3, 15, 5, 1]

@[expose] def bform6 (x y : ℕ) : ℕ := dotC 4 x (appC 4 gram6 y % 16)

@[expose] def okB6 (pre : List ℕ) (c : ℕ) : Bool :=
  (List.range pre.length).all fun i => bform6 c (pre.getD i 0) == bform6 (2 ^ pre.length) (2 ^ i)

@[expose] def fullB6 (cs : List ℕ) : Bool :=
  (List.range 16).all fun x => (List.range 16).all fun y =>
    bform6 (appC 4 cs x % 16) (appC 4 cs y % 16) == bform6 x y

theorem bform6_lt (x y : ℕ) : bform6 x y < 2 := by
  unfold bform6 dotC
  exact Nat.mod_lt _ (by norm_num)

theorem bform6_cast : ∀ x < 16, ∀ y < 16,
    (bform6 x y : ZMod 2) = Bf (vecN 4 x) (vecN 4 y) := by decide +kernel

theorem bform6_eq_of_cast {a b : ℕ} (h : (a : ZMod 2) = (b : ZMod 2)) (ha : a < 2) (hb : b < 2) :
    a = b := by
  have := (ZMod.natCast_eq_natCast_iff' _ _ 2).mp h
  omega

theorem mulVec_vecN_pow {d : ℕ} (K : Matrix (Fin d) (Fin d) (ZMod 2)) (j : Fin d) :
    K *ᵥ vecN d (2 ^ (j : ℕ)) = fun r => K r j := by
  have : vecN d (2 ^ (j : ℕ)) = Pi.single j 1 := by
    funext r
    simp [vecN, bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]
  rw [this, Matrix.mulVec_single_one]
  rfl

theorem hok6 (K : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hK : MemB K) :
    ∀ j < 4, okB6 ((colsOf 4 K).take j) ((colsOf 4 K).getD j 0) = true := by
  intro j hj
  unfold okB6
  rw [List.all_eq_true]
  intro i hi
  have hlen : ((colsOf 4 K).take j).length = j := by simp [colsOf_length, hj.le]
  rw [List.mem_range, hlen] at hi
  rw [hlen]
  simp only [beq_iff_eq]
  have hi' : i < 4 := by omega
  have e1 := colsOf_getD laws4 K ⟨j, hj⟩
  have e2 := colsOf_getD laws4 K ⟨i, hi'⟩
  have hget : ((colsOf 4 K).take j).getD i 0 = (colsOf 4 K).getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rw [hget]
  have hlt1 : (colsOf 4 K).getD j 0 < 16 := colsOf_getD_lt laws4 K hj
  have hlt2 : (colsOf 4 K).getD i 0 < 16 := colsOf_getD_lt laws4 K hi'
  have hp1 : 2 ^ j < 16 := by
    have : 2 ^ j < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) hj
    simpa using this
  have hp2 : 2 ^ i < 16 := by
    have : 2 ^ i < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) hi'
    simpa using this
  apply bform6_eq_of_cast _ (bform6_lt _ _) (bform6_lt _ _)
  rw [bform6_cast _ hlt1 _ hlt2, bform6_cast _ hp1 _ hp2, e1, e2,
    ← mulVec_vecN_pow K ⟨j, hj⟩, ← mulVec_vecN_pow K ⟨i, hi'⟩]
  exact hK _ _

theorem hfull6 (K : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hK : MemB K) :
    fullB6 (colsOf 4 K) = true := by
  unfold fullB6
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro x hx y hy
  have hx' : appC 4 (colsOf 4 K) x % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hy' : appC 4 (colsOf 4 K) y % 16 < 16 := Nat.mod_lt _ (by norm_num)
  apply bform6_eq_of_cast _ (bform6_lt _ _) (bform6_lt _ _)
  rw [bform6_cast _ hx' _ hy', bform6_cast _ hx _ hy]
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16, vecN_mod, vecN_mod, vecN_appC, vecN_appC, matOfCols_colsOf laws4 K]
  exact hK _ _

end Row6


namespace Row6

theorem hB6c : isOne 4 (mulC 4 (ccolsC 4 gm6 words6 u6) binv6) = true := by decide +kernel

theorem hw6 : words6.length = 4 := by decide

theorem hsearch6 : ∀ w < 2 ^ 4, condC 4 gm6 words6 binv6 w = true →
    ∀ cs ∈ bt 4 (fun pre c => okB6 pre c &&
      commOk 4 (pcolsC 4 gm6 words6 binv6 w) (pre ++ [c])) 4,
      leafC 4 gp6 fullB6 4 cs = true := by
  decide +kernel

end Row6


namespace Row6

open Equiv in
@[expose] def a6 : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

open Equiv in
@[expose] def b6 : Perm (Fin 6) := swap 0 2 * swap 4 5

theorem a6_mem : a6 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, a6]
  decide

theorem b6_mem : b6 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, b6]
  decide

@[expose] def xa : ↥(alternatingGroup (Fin 6)) := ⟨a6, a6_mem⟩

@[expose] def xb : ↥(alternatingGroup (Fin 6)) := ⟨b6, b6_mem⟩

theorem mat_a6 : mat6 a6 = matOfCols 4 [6, 1, 4, 9] := by decide +kernel

theorem mat_a6inv : mat6 a6⁻¹ = matOfCols 4 [2, 5, 4, 10] := by decide +kernel

theorem mat_b6 : mat6 b6 = matOfCols 4 [2, 1, 4, 12] := by decide +kernel

theorem mat_b6inv : mat6 b6⁻¹ = matOfCols 4 [2, 1, 4, 12] := by decide +kernel

@[expose] def gcs6 : List (↥(alternatingGroup (Fin 6)) × List ℕ) :=
  [(xa, [6, 1, 4, 9]), (xa⁻¹, [2, 5, 4, 10]), (xb, [2, 1, 4, 12]), (xb⁻¹, [2, 1, 4, 12])]

@[expose] def slist6 : List (List ℕ) :=
  [[1, 2, 4, 8], [6, 1, 4, 9], [2, 1, 4, 12], [2, 5, 4, 10], [5, 6, 4, 15], [5, 2, 4, 14],
    [1, 6, 4, 13], [6, 5, 4, 11]]

theorem slist6_one : ∃ c ∈ slist6, normC 4 c = normC 4 (oneC 4) := by decide +kernel

theorem slist6_cl : ∀ c ∈ slist6, ∀ p ∈ ([[6, 1, 4, 9], [2, 5, 4, 10], [2, 1, 4, 12],
    [2, 1, 4, 12]] : List (List ℕ)), ∃ c' ∈ slist6, normC 4 c' = normC 4 (mulC 4 p c) := by
  decide +kernel

theorem slist6_pow : ∀ c ∈ slist6, isOne 4 (sqIter 4 c 3) = true := by decide +kernel

end Row6


namespace Row6

theorem hgcs6 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (fr : Frame V L ↥(alternatingGroup (Fin 6)) 4) (hfr : ∀ γ, fr.mat γ = mat6 γ.1) :
    ∀ p ∈ gcs6, fr.mat p.1 = matOfCols 4 p.2 := by
  intro p hp
  simp only [gcs6, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rw [hfr]; exact mat_a6
  · rw [hfr]; exact mat_a6inv
  · rw [hfr]; exact mat_b6
  · rw [hfr]; exact mat_b6inv

theorem hinv6 : ∀ p ∈ gcs6, ∃ q ∈ gcs6, q.1 = p.1⁻¹ := by
  intro p hp
  simp only [gcs6, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨(xa⁻¹, [2, 5, 4, 10]), by simp [gcs6], rfl⟩
  · exact ⟨(xa, [6, 1, 4, 9]), by simp [gcs6], by simp⟩
  · exact ⟨(xb⁻¹, [2, 1, 4, 12]), by simp [gcs6], rfl⟩
  · exact ⟨(xb, [2, 1, 4, 12]), by simp [gcs6], by simp⟩

theorem slist6_cl' : ∀ c ∈ slist6, ∀ p ∈ gcs6, ∃ c' ∈ slist6,
    normC 4 c' = normC 4 (mulC 4 p.2 c) := by
  intro c hc p hp
  apply slist6_cl c hc
  simp only [gcs6, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp

@[expose] noncomputable def modelHyp6 {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (fr : Frame V L ↥(alternatingGroup (Fin 6)) 4) (hfr : ∀ γ, fr.mat γ = mat6 γ.1) :
    ModelHyp 4 ↥(alternatingGroup (Fin 6)) fr.mat where
  S0 := Subgroup.closure {x | x ∈ gcs6.map Prod.fst}
  p2 := isPGroup_closure laws4 fr.mat fr.mat_mul fr.mat_one (fun γ h => fr.eq_one_of_mat h) gcs6
    (hgcs6 fr hfr) hinv6 slist6 3 slist6_one slist6_cl' slist6_pow
  gens := [xa, xb]
  gens_mem := by
    intro g hg
    refine Subgroup.subset_closure ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp [gcs6]
  cyc := cycOf 4 gm6 u6 words6 binv6
  cyc_gm := by
    have hxa : fr.mat xa = matOfCols 4 [6, 1, 4, 9] := by rw [hfr]; exact mat_a6
    have hxb : fr.mat xb = matOfCols 4 [2, 1, 4, 12] := by rw [hfr]; exact mat_b6
    simp only [cycOf, gm6, List.map_cons, List.map_nil]
    rw [hxa, hxb]
  hB := hB_of laws4 gm6 u6 words6 binv6 hw6 hB6c
  Mem := MemB
  hMem := fun γ => by rw [hfr]; exact memB_mat6 γ.1
  a := 4
  hd := by norm_num
  leaf := by
    have hxa : fr.mat xa = matOfCols 4 [6, 1, 4, 9] := by rw [hfr]; exact mat_a6
    have hxb : fr.mat xb = matOfCols 4 [2, 1, 4, 12] := by rw [hfr]; exact mat_b6
    have hxai : fr.mat xa⁻¹ = matOfCols 4 [2, 5, 4, 10] := by rw [hfr]; exact mat_a6inv
    have hxbi : fr.mat xb⁻¹ = matOfCols 4 [2, 1, 4, 12] := by rw [hfr]; exact mat_b6inv
    have hgp : [xa, xb].map (fun s => (fr.mat s, fr.mat s⁻¹)) =
        gp6.map fun p => (matOfCols 4 p.1, matOfCols 4 p.2) := by
      simp only [gp6, List.map_cons, List.map_nil]
      rw [hxa, hxb, hxai, hxbi]
    rw [hgp]
    exact leaf_of_search laws4 gm6 gp6 u6 words6 binv6 hw6 okB6 fullB6 4 MemB hok6 hfull6
      hsearch6

end Row6


namespace Row6

theorem exists_frame6 {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}
    (hB4 : B4Hyp G L) (hrow : B42Case6 G L A ∨ BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1) :
    ∃ fr : Frame V L ↥(alternatingGroup (Fin 6)) 4, ∀ γ, fr.mat γ = mat6 γ.1 := by
  obtain ⟨e, ψ, hψ, he⟩ := alt6_data hB4 hrow
  refine ⟨⟨e.trans kappa, ψ, hψ, fun γ => mat6 γ.1, fun γ w => ?_⟩, fun γ => rfl⟩
  show Multiplicative.toAdd (kappa (e (((ψ γ : ↥L) : MulAut V) w))) =
    mat6 γ.1 *ᵥ Multiplicative.toAdd (kappa (e w))
  rw [he, kappa_aut]

end Row6

end CFSG.Quasithin.H13.A6.GR

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank in
theorem factCommA6 : FactCommA6 := by
  intro V _ _ hV G L A hB4 hrow v hcond hrk S X hS hSv hXL hXv hSX hXO hX1
  obtain ⟨fr, hfr⟩ := GR.Row6.exists_frame6 hB4 hrow
  exact GR.comm_core fr (GR.Row6.modelHyp6 fr hfr) hcond.sq hrk hS hSv hXL hXv hSX hXO hX1

end CFSG.Quasithin.H13.A6

