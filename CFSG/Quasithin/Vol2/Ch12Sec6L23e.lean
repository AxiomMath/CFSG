module

public import CFSG.Quasithin.Vol2.Ch12Sec6L23a
public import CFSG.Quasithin.Vol2.Ch12Sec6L23b
public import CFSG.Quasithin.Vol2.Ch12Sec6L23c
public import CFSG.Quasithin.Vol2.Ch12Sec6L23d
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma1
public import CFSG.Quasithin.Vol2.Ch12Sec6L22F

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126P Equiv A5Mod CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

namespace S126L23e

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem centralizer_eq_bot (h331 : Stmt3_3_1)
    (h3228 : Stmt3_2_2_eight) (h1222 : Stmt12_2_2) (h1227 : Stmt12_2_7) (h1228 : Stmt12_2_8)
    (h1229 : Stmt12_2_9) (h1232 : Cor12_3_2) (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19)
    (hS8 : FactS8ElemAbE8) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hZ
  have hyp := hH.hyp
  obtain ⟨hVT, hTV, hVe, hV1, hMV⟩ := S126L23a.basics h1222 F hH
  have hCZ := S126L23a.centralizer_Z_le h1222 h1229 F hH hZ
  obtain ⟨⟨-, hLTM, -⟩, ⟨H, hHs⟩, hUall⟩ := S126L23a.stmt331 h331 hH
  have hU := hUall H hHs
  have hns := S126L23a.not_solvable h331 h3228 h1222 h1262 h1219 hS8 F hH hZ hHs
  obtain ⟨g, hgT, hgC, hgV⟩ :=
    S126L23a.exists_A h331 h3228 h1222 h1227 h1262 h1219 hS8 F hH hZ hCZ hHs
  have hTH : T ≤ H := hHs.1.1
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans hLTM
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set A := conjSubgroup V g with hAdef
  obtain ⟨⟨hred2, hCT, -, -⟩, -⟩ := h1227 G T L V H hyp hCZ hHs
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    ((Subgroup.closure_le _).mpr fun _ hz => hz.1).trans inf_le_left
  have hVHH : VZ T H ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hTH (hZT hz))) (H.inv_mem hh)
  have hredVH : IsTwoReducedIn H (VZ T H) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVHH, hred2⟩
  have hVHel : IsElemAbelian 2 (VZ T H) := hredVH.2.2.1
  have hHN : H ≤ Subgroup.normalizer (VZ T H : Set G) := hredVH.2.1
  set VH := VZ T H with hVHdef
  rcases h1232 G T L V H hyp hCZ hHs with hsol | ⟨hLie, -, -, hsum⟩
  · exact hns hsol
  set K := oTwoUpper H with hKdef
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have h2K : ∀ h ∈ H, ∃ j : ℕ, h ^ 2 ^ j ∈ oTwoUpper H := fun h hh =>
    exists_pow_mem_oTwoUpper H hh
  have hsylH : CFSG.QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  rw [← VZ_eq_VZ_oTwoUpper hsylH] at hsum
  obtain ⟨W, hW, hWle⟩ : ∃ W : Subgroup G, IsA5ModuleUnder (oTwoUpper H) W ∧
      W ≤ ⁅VZ T H, oTwoUpper H⁆ := by
    rcases hsum with h | ⟨W₁, W₂, hW₁, -, -, hsup⟩
    · exact ⟨_, h, le_rfl⟩
    · exact ⟨W₁, hW₁, hsup ▸ le_sup_left⟩
  have hWV : W ≤ VZ T H :=
    hWle.trans (commutator_le_of_le_normalizer (hKH.trans hHN))
  have hO2K : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.centralizer (VZ T H : Set G) := by
    have h1 : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H := F7.pCoreOf_mono_of_le_normalizer hKH hHK
    rw [← hCT] at h1
    exact h1.trans inf_le_right
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hLie
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hCW := inf_centralizer_le_of_a5Module hW hWV e.isSimpleGroup hO2K
  obtain ⟨d⟩ := A5Mod.exists_data hW
  obtain ⟨σ, hσker, hσK⟩ := S126L23b.exists_sigma d hKH hHK h2K hredVH hWV hCW
  have hcardK : Nat.card K = 60 * Nat.card ↥(K ⊓ Subgroup.centralizer (W : Set G)) := by
    have hker : d.q.ker = (Subgroup.centralizer (W : Set G)).subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact d.q_eq_one k
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup d.q.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective d.q d.q_surj).toEquiv,
      S126L23b.card_A5, hker, ← Subgroup.inf_subgroupOf_left] at h1
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hcardK' : Nat.card K = 60 * Nat.card ↥(pCoreOf 2 K) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    rw [Nat.card_congr e.toEquiv, S126L23b.card_A5] at h1
    rw [h1]
    congr 1
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ K.subtype Subtype.val_injective).toEquiv
  have hKCW : K ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 K := by
    have hle : pCoreOf 2 K ≤ K ⊓ Subgroup.centralizer (W : Set G) :=
      le_inf (LieType.BorelTits.pCoreOf_le 2 K) (hO2K.trans (Subgroup.centralizer_le hWV))
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  have hKCW2 : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (W : Set G)) := by
    rw [hKCW]
    exact LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hCH2 : IsPGroup 2 ↥(H ⊓ Subgroup.centralizer (VH : Set G)) := by
    rintro ⟨x, hxH, hxC⟩
    obtain ⟨j, hj⟩ := h2K x hxH
    have hxj : x ^ 2 ^ j ∈ K ⊓ Subgroup.centralizer (W : Set G) :=
      ⟨hj, Subgroup.centralizer_le hWV (Subgroup.pow_mem _ hxC _)⟩
    obtain ⟨m, hm⟩ := hKCW2 ⟨_, hxj⟩
    refine ⟨j + m, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1 ⊢
    rw [pow_add, pow_mul]
    exact h1
  have hCHN : H ≤ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (VH : Set G) : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (hHN.trans (F7.normalizer_le_normalizer_centralizer VH))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hCHT : H ⊓ Subgroup.centralizer (VH : Set G) ≤ T := by
    have h1 := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCHN hCH2
    rw [← hCT] at h1
    exact h1.trans inf_le_left
  have hσKmem : ∀ k : G, ∀ hk : k ∈ K, σ ⟨k, hKH hk⟩ ∈ alt5 := fun k hk => by
    rw [hσK ⟨k, hKH hk⟩ hk]
    exact d.qG_mem_alt5 hk
  have hσKsurj : ∀ p ∈ alt5, ∃ k : G, ∃ hk : k ∈ K, σ ⟨k, hKH hk⟩ = p := fun p hp => by
    obtain ⟨k, hk, hkp⟩ := d.exists_qG_eq hp
    exact ⟨k, hk, by rw [hσK ⟨k, hKH hk⟩ hk]; exact hkp⟩
  have hσH1 : ∀ h : ↥H, σ h = 1 → (h : G) ∈ T := fun h h1 =>
    hCHT ⟨h.2, (hσker h).1 h1⟩
  have hsylTK : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hsylH hKH hHK
  let ρ : ↥K →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp d.q
  have hρr : ρ.range = alternatingGroup (Fin 5) := by
    ext p
    constructor
    · rintro ⟨k, rfl⟩
      exact (d.q k).2
    · intro hp
      obtain ⟨k, hk⟩ := d.q_surj ⟨p, hp⟩
      exact ⟨k, by simp [ρ, hk]⟩
  set E := ((T ⊓ K).subgroupOf K).map ρ with hEdef
  have hsylE := S126L23b.isSylowTwoOf_map' hsylTK ρ
  rw [hρr] at hsylE
  have hE4 : Nat.card E = 4 := by
    have := S126L1c.card_of_isSylowTwoOf hsylE (a := 2) (m := 15)
      (by rw [S126L23b.card_A5]; norm_num) (by decide)
    rw [this]
    norm_num
  have hEA : E ≤ alternatingGroup (Fin 5) := hsylE.1
  set S := (T.subgroupOf H).map σ with hSdef
  have hσρ : ∀ k : ↥K, ρ k = σ ⟨k, hKH k.2⟩ := fun k => by
    rw [hσK ⟨k, hKH k.2⟩ k.2]
    exact (d.qG_coe k).symm
  have hES : E ≤ S := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.1 hk
    exact Subgroup.mem_map.2 ⟨⟨k, hKH k.2⟩, Subgroup.mem_subgroupOf.2 hk'.1, (hσρ k).symm⟩
  have hS2 : IsPGroup 2 S := by
    have hT2 : IsPGroup 2 (T.subgroupOf H) :=
      hsylH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
    exact hT2.map σ
  have hSE := S126L23b.mem_of_mem_alt5 hS2 hES hEA hE4
  obtain ⟨p, hpI, q, hqI, hK, hpE, hqE, hEl⟩ := S126L23b.klein_of_card_four hEA hE4
  have hSE' : ∀ s ∈ S, s ∈ alt5 → s ∈ [1, p, q, p * q] := fun s hs hsA => hEl s (hSE s hs hsA)
  have hEset : ∀ x, x ∈ E ↔ x ∈ [1, p, q, p * q] := fun x => ⟨hEl x, fun hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [E.one_mem, hpE, hqE, E.mul_mem hpE hqE]⟩
  have hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (E : Set (Perm (Fin 5))) := by
    have key : ∀ s ∈ S, ∀ x ∈ E, s * x * s⁻¹ ∈ E := fun s hs x hx =>
      hSE _ (S.mul_mem (S.mul_mem hs (hES hx)) (S.inv_mem hs)) (by
        rw [S126L23b.mem_alt5_iff] at *
        exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem x (hEA hx) s)
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key s hs x, fun hx => ?_⟩
    have := key s⁻¹ (S.inv_mem hs) _ hx
    rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at this
  obtain ⟨c', hc'A, hc'1, hc'3, hc'E⟩ := S126L23b.exists_three p hpI q hqI hK
  have hc'N : c' ∈ Subgroup.normalizer (E : Set (Perm (Fin 5))) := by
    have e2 : c' * c' = c'⁻¹ := eq_inv_of_mul_eq_one_left hc'3
    have e1 : c'⁻¹ * c'⁻¹ = c' := by rw [← mul_inv_rev, e2, inv_inv]
    have h1 : ∀ x ∈ E, c'⁻¹ * x * c' ∈ E := fun x hx =>
      (hEset _).2 (hc'E x ((hEset x).1 hx))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := h1 _ (h1 x hx)
      rwa [show c'⁻¹ * (c'⁻¹ * x * c') * c' = (c'⁻¹ * c'⁻¹) * x * (c' * c') by group, e1,
        e2] at this
    · intro hx
      have := h1 _ hx
      rwa [show c'⁻¹ * (c' * x * c'⁻¹) * c' = x by group] at this
  let P : Subgroup ↥H := (Subgroup.normalizer (E : Set (Perm (Fin 5)))).comap σ
  have hTP : T ≤ P.map H.subtype := fun t ht =>
    Subgroup.mem_map.2 ⟨⟨t, hTH ht⟩, hSN _ (Subgroup.mem_map_of_mem σ
      (Subgroup.mem_subgroupOf.2 ht)), rfl⟩
  have hPH : P.map H.subtype < H := by
    refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun h => ?_
    obtain ⟨g₀, hg₀A, hg₀⟩ := S126L23b.not_normal p hpI q hqI hK
    obtain ⟨k, hk, hkσ⟩ := hσKsurj g₀ hg₀A
    have hkP : (⟨k, hKH hk⟩ : ↥H) ∈ P := by
      have hkm : k ∈ P.map H.subtype := by
        rw [h]
        exact hKH hk
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hkm
      have : y = ⟨k, hKH hk⟩ := Subtype.ext hye
      rwa [← this]
    have h1 := (Subgroup.mem_normalizer_iff.1 hkP p).1 hpE
    rw [hkσ] at h1
    exact hg₀ ((hEset _).1 h1)
  have hPM : P.map H.subtype ≤ H ⊓ M := by
    obtain ⟨N, hN, hPN⟩ := exists_isMaxSubgroupIn hPH
    rw [← (isUniqueMaxOver_iff.mp hU).2.2 N hN (hTP.trans hPN)]
    exact hPN
  obtain ⟨c, hcK, hcσ⟩ := hσKsurj c' hc'A
  have hcHM : c ∈ H ⊓ M := hPM (Subgroup.mem_map.2 ⟨⟨c, hKH hcK⟩, by
    show σ ⟨c, hKH hcK⟩ ∈ Subgroup.normalizer (E : Set (Perm (Fin 5)))
    rw [hcσ]
    exact hc'N, rfl⟩)
  set X := ((H ⊓ M).subgroupOf H).map σ with hXdef
  have hTHM : T ≤ H ⊓ M := le_inf hTH hTM
  have hEX : E ≤ X := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.1 hk
    exact Subgroup.mem_map.2 ⟨⟨k, hKH k.2⟩, Subgroup.mem_subgroupOf.2 (hTHM hk'.1), (hσρ k).symm⟩
  have hc'X : c' ∈ X := Subgroup.mem_map.2 ⟨⟨c, hKH hcK⟩, Subgroup.mem_subgroupOf.2 hcHM, hcσ⟩
  have hHTK : T ⊔ K = H := by
    have hres : twoResidual H ≤ K :=
      twoResidual_le_of_isTwoQuotient (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
        fun y hy => exists_pow_mem_oTwoUpper H hy
    exact le_antisymm (sup_le hTH hKH)
      ((sup_twoResidual_eq hsylH).symm.le.trans (sup_le_sup_left hres T))
  have hY5 : Nat.card ↥(X ⊓ alternatingGroup (Fin 5)) = 12 := by
    have h4 : 4 ∣ Nat.card ↥(X ⊓ alternatingGroup (Fin 5)) :=
      hE4 ▸ Subgroup.card_dvd_of_le (le_inf hEX hEA)
    have hc'Y : c' ∈ X ⊓ alternatingGroup (Fin 5) := ⟨hc'X, S126L23b.mem_alt5_iff.1 hc'A⟩
    have h3 : 3 ∣ Nat.card ↥(X ⊓ alternatingGroup (Fin 5)) := by
      have hord : orderOf (⟨c', hc'Y⟩ : ↥(X ⊓ alternatingGroup (Fin 5))) = 3 := by
        rw [Subgroup.orderOf_mk]
        refine orderOf_eq_prime ?_ hc'1
        rw [pow_three, ← mul_assoc]
        exact hc'3
      rw [← hord]
      exact orderOf_dvd_natCard _
    have h60 : Nat.card ↥(X ⊓ alternatingGroup (Fin 5)) ∣ 60 :=
      S126L23b.card_A5 ▸ Subgroup.card_dvd_of_le inf_le_right
    have h12 : 12 ∣ Nat.card ↥(X ⊓ alternatingGroup (Fin 5)) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
    obtain ⟨k, hk⟩ := h12
    rw [hk] at h60
    have hk5 : k ∣ 5 := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 12)).1 (by simpa using h60)
    rcases (Nat.dvd_prime (by norm_num)).1 hk5 with rfl | rfl
    · rw [hk]
    · exfalso
      have hAX : alternatingGroup (Fin 5) ≤ X := by
        have heq : X ⊓ alternatingGroup (Fin 5) = alternatingGroup (Fin 5) :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk, S126L23b.card_A5])
        exact heq ▸ inf_le_left
      have hKM : K ≤ H ⊓ M := by
        intro k hk
        obtain ⟨x, hx, hxσ⟩ := Subgroup.mem_map.1
          (hAX (S126L23b.mem_alt5_iff.1 (hσKmem k hk)))
        have h1 : σ (x⁻¹ * ⟨k, hKH hk⟩) = 1 := by rw [map_mul, map_inv, hxσ, inv_mul_cancel]
        have h2 := hσH1 _ h1
        have h3 : (x : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.1 hx
        have e : k = (x : G) * ((x⁻¹ * ⟨k, hKH hk⟩ : ↥H) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact (H ⊓ M).mul_mem h3 (hTHM h2)
      exact hHs.2.1 ((hHTK.symm.le.trans (sup_le hTHM hKM)).trans inf_le_right)
  have hX5 : ∀ x ∈ X, x ^ 5 = 1 → x = 1 := by
    intro x hx h5
    have hxY : x ∈ X ⊓ alternatingGroup (Fin 5) :=
      ⟨hx, S126L23b.mem_alt5_iff.1 (S126L23b.five_even x h5)⟩
    have h1 : orderOf (⟨x, hxY⟩ : ↥(X ⊓ alternatingGroup (Fin 5))) ∣ 12 :=
      hY5 ▸ orderOf_dvd_natCard _
    have h2 : orderOf (⟨x, hxY⟩ : ↥(X ⊓ alternatingGroup (Fin 5))) ∣ 5 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one h5
    have h3 : orderOf (⟨x, hxY⟩ : ↥(X ⊓ alternatingGroup (Fin 5))) = 1 :=
      Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 12 5) h1 h2
    rw [orderOf_eq_one_iff] at h3
    exact congrArg Subtype.val h3
  have hL3 := S126L1a.part5 h1222 h1228 hH
  have h3L : ∀ y ∈ M, y ^ 3 = 1 → y ∈ L := fun y hy h3 => by
    rw [← hL3]
    exact Subgroup.subset_closure ⟨hy, 1, by simpa using h3⟩
  have hodd : ∀ x ∈ H ⊓ M, ∀ m : ℕ, Odd m → x ^ m = 1 → x ∈ L := by
    intro x hx m hm hxm
    let xh : ↥H := ⟨x, hx.1⟩
    have hxX : σ xh ∈ X := Subgroup.mem_map_of_mem σ (Subgroup.mem_subgroupOf.2 hx)
    have hm' : σ xh ^ m = 1 := by
      rw [← map_pow]
      have : xh ^ m = 1 := Subtype.ext (by simpa [xh] using hxm)
      rw [this, map_one]
    have h120 : σ xh ^ 120 = 1 := by
      have := pow_card_eq_one (G := Perm (Fin 5)) (x := σ xh)
      rwa [Fintype.card_perm, Fintype.card_fin] at this
    have h15 : σ xh ^ 15 = 1 := by
      have hg := pow_gcd_eq_one.2 ⟨hm', h120⟩
      have hd : Nat.gcd m 120 ∣ 15 := by
        have h1 : Nat.Coprime (Nat.gcd m 120) 8 := by
          have : Nat.Coprime m 8 := by
            rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
            exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hm)
          exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left m 120) this
        have h2 : Nat.gcd m 120 ∣ 8 * 15 := Nat.gcd_dvd_right m 120
        exact h1.dvd_of_dvd_mul_left h2
      obtain ⟨t, ht⟩ := hd
      rw [ht, pow_mul, hg, one_pow]
    have h3 : σ xh ^ 3 = 1 := by
      rcases S126L23b.odd15 _ h15 with h | h
      · exact h
      · rw [hX5 _ hxX h, one_pow]
    have hx3C : x ^ 3 ∈ H ⊓ Subgroup.centralizer (VH : Set G) := by
      have h1 : σ (xh ^ 3) = 1 := by rw [map_pow, h3]
      exact ⟨H.pow_mem hx.1 3, by simpa [xh] using (hσker _).1 h1⟩
    obtain ⟨j, hj⟩ := hCH2 ⟨_, hx3C⟩
    have hj' : (x ^ 3) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hm3 : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
    have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
    have hx3 : x ^ 3 = 1 := by
      have := pow_gcd_eq_one.2 ⟨hj', hm3⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    exact h3L x hx.2 hx3
  have hres : twoResidual (H ⊓ M) ≤ L := by
    refine (iInf₂_le ((H ⊓ M) ⊓ L) ⟨inf_le_left, ?_, ?_⟩).trans inf_le_right
    · exact (le_inf Subgroup.le_normalizer (inf_le_right.trans le_rfl)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · intro x hx
      obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
      refine ⟨a, (H ⊓ M).pow_mem hx _, hodd _ ((H ⊓ M).pow_mem hx _) m hm ?_⟩
      rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  have hHMsyl : CFSG.QuasithinUnique.IsSylowTwoOf T (H ⊓ M) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTHM
  have hHMLT : H ⊓ M ≤ L ⊔ T := by
    rw [← sup_twoResidual_eq hHMsyl]
    exact sup_le le_sup_right (hres.trans le_sup_left)
  have hVcl : conjClosure V T = V :=
    le_antisymm (conjClosure_le fun _ ht _ hz => (Subgroup.mem_normalizer_iff.mp (hTV ht) _).mp hz)
      (le_conjClosure V T)
  obtain ⟨-, -, hO⟩ := h3228 G T L V hyp.fsu
  rw [hyp.conjClosure_eq, hVcl] at hO
  have hAR : A ≤ pCoreOf 2 (L ⊔ T) ⊓ (H ⊓ M) :=
    le_inf (hO ▸ le_inf hgT hgV) (hgT.trans hTHM)
  have hRN : H ⊓ M ≤ Subgroup.normalizer
      ((pCoreOf 2 (L ⊔ T) ⊓ (H ⊓ M) : Subgroup G) : Set G) :=
    (le_inf (hHMLT.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hRT : pCoreOf 2 (L ⊔ T) ⊓ (H ⊓ M) ≤ T := inf_le_left.trans (hO ▸ inf_le_left)
  have hAH : A ≤ H := hgT.trans hTH
  have hσA : ∀ a : G, ∀ ha : a ∈ A, σ ⟨a, hAH ha⟩ ∈ alt5 := by
    intro a ha
    have hcaR : c⁻¹ * a * c ∈ pCoreOf 2 (L ⊔ T) ⊓ (H ⊓ M) := by
      have := (Subgroup.mem_normalizer_iff.1 (hRN ((H ⊓ M).inv_mem hcHM)) a).1 (hAR ha)
      simpa using this
    refine S126L23b.mem_alt5_of_conj hS2 hpI hqI hK (hES hpE) (hES hqE) hSE' hc'1 hc'3 hc'E
      (Subgroup.mem_map.2 ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.2 (hgT ha), rfl⟩) ?_
    have e : c'⁻¹ * σ ⟨a, hAH ha⟩ * c' =
        σ ⟨c⁻¹ * a * c, H.mul_mem (H.mul_mem (H.inv_mem (hKH hcK)) (hAH ha)) (hKH hcK)⟩ := by
      rw [← hcσ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact Subgroup.mem_map.2 ⟨_, Subgroup.mem_subgroupOf.2 (hRT hcaR), rfl⟩
  have hAel : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hVe g
  have hApg : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hAel.2 x x.2)⟩
  set B := A ⊓ Subgroup.centralizer (VH : Set G) with hBdef
  let σA : ↥A →* Perm (Fin 5) := σ.comp (Subgroup.inclusion hAH)
  have hσAker : σA.ker = B.subgroupOf A := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show σ ⟨y, hAH y.2⟩ = 1 ↔ (y : G) ∈ A ⊓ Subgroup.centralizer (VH : Set G)
    rw [hσker]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
  have hidx : B.relIndex A = Nat.card σA.range := by
    rw [Subgroup.relIndex, ← hσAker, Subgroup.index_ker]
  have hσAr : σA.range ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨y, rfl⟩
    exact S126L23b.mem_alt5_iff.1 (hσA y y.2)
  have hσA2 : IsPGroup 2 σA.range := hApg.of_surjective σA.rangeRestrict σA.rangeRestrict_surjective
  have hσA4 : Nat.card σA.range ≤ 4 := S126L23b.card_le_four hσA2 hσAr
  have hmB : E3.mQuot A B ≤ 2 := by
    have h1 : 2 ^ E3.mQuot A B ≤ 2 ^ 2 := by
      rw [← E3.relIndex_eq_two_pow hApg B, hidx]
      exact hσA4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hr := (lemma12_6_20_of h331 h1222 h1262 h1219 G T L V F hH).2.2 hZ
  have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    by_contra hcon
    have h1 := E3.rParam_le_mQuot (inf_le_left : B ≤ A) hcon
    rw [hAdef, E3.rParam_conj V g] at h1
    have h2 : (E3.mQuot (conjSubgroup V g) B : ℕ∞) ≤ 2 := by exact_mod_cast hmB
    have h3 := hr.trans (h1.trans h2)
    norm_num at h3
  have hVHA : VH ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.le_centralizer_iff.1 inf_le_right).trans hCB
  have hquad : ∀ v ∈ VH, ∀ a ∈ A, ∀ b ∈ A,
      b * (a * v * a⁻¹ * v⁻¹) * b⁻¹ = a * v * a⁻¹ * v⁻¹ := by
    intro v hv a ha b hb
    have h1 : v * a⁻¹ * v⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hVHA hv) _).1 (A.inv_mem ha)
    have h2 : a * v * a⁻¹ * v⁻¹ ∈ A := by
      rw [show a * v * a⁻¹ * v⁻¹ = a * (v * a⁻¹ * v⁻¹) by group]
      exact A.mul_mem ha h1
    have hc := hAel.1
    have h3 : b * (a * v * a⁻¹ * v⁻¹) = (a * v * a⁻¹ * v⁻¹) * b :=
      congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : ↥A) ⟨_, h2⟩)
    rw [h3, mul_inv_cancel_right]
  have hactW : ∀ a : G, ∀ ha : a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W ∧
      d.β (a * w * a⁻¹) = act5 (σ ⟨a, hAH ha⟩) (d.β w) := by
    intro a ha w hw
    obtain ⟨k, hk, hkq, hkC⟩ := S126L23b.exists_K_of_alt5 d hKH hσker hσK (hσA a ha)
    have hkw : k * w * k⁻¹ ∈ W := d.conj_mem' hk hw
    have e : a * w * a⁻¹ = k * w * k⁻¹ := by
      have h1 := Subgroup.mem_centralizer_iff.1 hkC _ (hWV hkw)
      calc a * w * a⁻¹ = (a * k⁻¹) * (k * w * k⁻¹) * (a * k⁻¹)⁻¹ := by group
        _ = (k * w * k⁻¹) * (a * k⁻¹) * (a * k⁻¹)⁻¹ := by rw [← h1]
        _ = k * w * k⁻¹ := by group
    rw [e]
    exact ⟨hkw, by rw [d.β_conj' hk hw, hkq]⟩
  have hβinv : ∀ w ∈ W, d.β w⁻¹ = d.β w := by
    intro w hw
    have h1 := d.β_mul w hw w⁻¹ (W.inv_mem hw)
    rw [mul_inv_cancel, d.β_one] at h1
    have h2 : d.β w⁻¹ = -d.β w := by rw [eq_neg_iff_add_eq_zero, add_comm, ← h1]
    rw [h2]
    funext i
    simp only [Pi.neg_apply]
    exact ZModModule.neg_eq_self (d.β w i)
  have hσA2' : Nat.card σA.range ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h4 : Nat.card σA.range = 4 := by
      obtain ⟨n, hn⟩ := hσA2.exists_card_eq
      rw [hn] at hcon hσA4 ⊢
      have : n = 2 := by
        rcases n with _ | _ | _ | n
        · norm_num at hcon
        · norm_num at hcon
        · rfl
        · exfalso
          have : 2 ^ (n + 3) ≥ 8 := by
            calc 2 ^ (n + 3) ≥ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
              _ = 8 := by norm_num
          omega
      rw [this]
      norm_num
    obtain ⟨p', hp'I, q', hq'I, hK', hp'R, hq'R, -⟩ := S126L23b.klein_of_card_four hσAr h4
    obtain ⟨⟨a, ha⟩, hap⟩ := hp'R
    obtain ⟨⟨b, hb⟩, hbq⟩ := hq'R
    obtain ⟨x, hx, hxq⟩ := S126L23b.not_quad p' hp'I q' hq'I hK'
    obtain ⟨w, hw, hwx⟩ := d.β_surj x hx
    obtain ⟨haw, haβ⟩ := hactW a ha w hw
    have hu : a * w * a⁻¹ * w⁻¹ ∈ W := W.mul_mem haw (W.inv_mem hw)
    have huβ : d.β (a * w * a⁻¹ * w⁻¹) = act5 p' x + x := by
      rw [d.β_mul _ haw _ (W.inv_mem hw), haβ, hβinv w hw, hwx]
      rw [← hap]
      rfl
    obtain ⟨-, hbβ⟩ := hactW b hb _ hu
    have hq := hquad w (hWV hw) a ha b hb
    rw [hq, huβ] at hbβ
    apply hxq
    have e : σ ⟨b, hAH hb⟩ = q' := hbq
    rw [← e]
    exact hbβ.symm
  obtain ⟨a₀, ha₀A, ha₀C⟩ : ∃ a₀ ∈ A, a₀ ∉ Subgroup.centralizer (VH : Set G) := by
    by_contra h
    push Not at h
    exact hgC h
  have hσa₀ : σ ⟨a₀, hAH ha₀A⟩ ≠ 1 := fun h => ha₀C ((hσker _).1 h)
  have hBA : B.relIndex A = 2 := by
    rw [hidx]
    have h1 : σA.range ≠ ⊥ := fun h => by
      have : σA ⟨a₀, ha₀A⟩ ∈ σA.range := ⟨_, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact hσa₀ this
    have h2 := (Subgroup.one_lt_card_iff_ne_bot _).2 h1
    omega
  obtain ⟨E8⟩ := S126FE.exists_frame126E h1222 F hH hZ
  have hNVL := S126L20c.normalizer_V_le h331 h1222 F hH
  have hkey : ∀ y : G, g⁻¹ * y * g ∈ A ↔ y ∈ V := fun y => by
    rw [hAdef, mem_conjSubgroup_iff, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
  have hxN : ∀ v ∈ VH, g * v * g⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [← hkey u, ← hkey (g * v * g⁻¹ * u * (g * v * g⁻¹)⁻¹),
      show g⁻¹ * (g * v * g⁻¹ * u * (g * v * g⁻¹)⁻¹) * g = v * (g⁻¹ * u * g) * v⁻¹ by group]
    exact Subgroup.mem_normalizer_iff.1 (hVHA hv) _
  set B' := B.map (MulAut.conj g).toMonoidHom with hB'def
  have hAV : A.map (MulAut.conj g).toMonoidHom = V := by
    rw [hAdef, conjSubgroup, Subgroup.map_map]
    convert Subgroup.map_id V
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hB'V : B'.relIndex V = 2 := by
    rw [← hAV, hB'def, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hBA]
  set H₀ : Subgroup ↥(G6.coreMod 8) := (B'.subgroupOf V).map E8.γ.toMonoidHom with hH₀def
  have hH₀ : H₀.index = 2 := by
    rw [hH₀def]
    exact (Subgroup.index_map_equiv (B'.subgroupOf V) E8.γ).trans hB'V
  have hfix : ∀ v ∈ VH, ∀ τ : Perm (Fin 8), ActsAs F (g * v * g⁻¹) τ →
      ∀ m ∈ H₀, G6.coreAct 8 τ m = m := by
    intro v hv τ hτ m hm
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hm
    have hu' : (u : G) ∈ B' := Subgroup.mem_subgroupOf.1 hu
    obtain ⟨b, hb, hbu⟩ := Subgroup.mem_map.1 hu'
    have hbv : v * b = b * v := Subgroup.mem_centralizer_iff.1 hb.2 v hv
    have hc : (u : G) = g * v * g⁻¹ * u * (g * v * g⁻¹)⁻¹ := by
      rw [← hbu]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * b * g⁻¹ = g * (v * b) * v⁻¹ * g⁻¹ := by rw [hbv]; group
        _ = g * v * g⁻¹ * (g * b * g⁻¹) * (g * v * g⁻¹)⁻¹ := by group
    exact (E8.act _ (hNVL (hxN v hv)) (hxN v hv) τ hτ u u hc).symm
  have hne1 : ∀ v ∈ VH, v ∉ Subgroup.centralizer (A : Set G) → ∀ τ : Perm (Fin 8),
      ActsAs F (g * v * g⁻¹) τ → τ ≠ 1 := by
    intro v hv hvA τ hτ h1
    apply hvA
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haV : g * a * g⁻¹ ∈ V := by
      rw [← hkey]
      simpa [mul_assoc] using ha
    have h2 := E8.act _ (hNVL (hxN v hv)) (hxN v hv) τ hτ ⟨_, haV⟩
      ⟨g * v * g⁻¹ * (g * a * g⁻¹) * (g * v * g⁻¹)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (hxN v hv) _).1 haV⟩ rfl
    rw [h1, map_one, MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val (E8.γ.injective h2)
    simp only at h3
    have e : g * v * g⁻¹ * (g * a * g⁻¹) * (g * v * g⁻¹)⁻¹ = g * (v * a * v⁻¹) * g⁻¹ := by group
    rw [e] at h3
    have h4 : v * a * v⁻¹ = a := mul_left_cancel (mul_right_cancel h3)
    calc a * v = (v * a * v⁻¹) * v := by rw [h4]
      _ = v * a := by group
  have hVHcard : Nat.card VH ≤ 2 * Nat.card ↥(VH ⊓ Subgroup.centralizer (A : Set G)) := by
    refine S126L23c.card_le_two_mul inf_le_left fun v hv w hw hvC hwC => ?_
    have hvA : v ∉ Subgroup.centralizer (A : Set G) := fun h => hvC ⟨hv, h⟩
    have hwA : w ∉ Subgroup.centralizer (A : Set G) := fun h => hwC ⟨hw, h⟩
    obtain ⟨τv, hτv⟩ := S126N.exists_actsAs F hH (hNVL (hxN v hv)) (hxN v hv)
    obtain ⟨τw, hτw⟩ := S126N.exists_actsAs F hH (hNVL (hxN w hw)) (hxN w hw)
    have heq : τv = τw := S126L23c.eq_of_fix_index_two hH₀ (hfix v hv τv hτv)
      (hfix w hw τw hτw) (hne1 v hv hvA τv hτv) (hne1 w hw hwA τw hτw)
    have hvv : v * v = 1 := by
      have := hVHel.2 v hv
      rwa [pow_two] at this
    have hsq : τv * τv = 1 := by
      have h1 := hτv.mul hτv (hxN v hv)
      have e : g * v * g⁻¹ * (g * v * g⁻¹) = 1 := by
        rw [show g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ by group, hvv]
        group
      rw [e] at h1
      exact ActsAs.unique h1 (ActsAs.one F) (Subgroup.one_mem _)
    have hvw : ActsAs F (g * (v * w) * g⁻¹) 1 := by
      have h1 := hτv.mul hτw (hxN w hw)
      rw [← heq, hsq] at h1
      rwa [show g * v * g⁻¹ * (g * w * g⁻¹) = g * (v * w) * g⁻¹ by group] at h1
    refine ⟨VH.mul_mem hv hw, ?_⟩
    by_contra hvwA
    exact hne1 (v * w) (VH.mul_mem hv hw) hvwA 1 hvw rfl
  have hp₀A := hσA a₀ ha₀A
  have hp₀I : σ ⟨a₀, hAH ha₀A⟩ ∈ invs5 := by
    rw [mem_invs5, ← map_mul]
    have : (⟨a₀, hAH ha₀A⟩ : ↥H) * ⟨a₀, hAH ha₀A⟩ = 1 :=
      Subtype.ext (by simpa [pow_two] using hAel.2 a₀ ha₀A)
    rw [this, map_one]
  have hcf := S126L23b.card_fix _ hp₀I hp₀A hσa₀
  have hW16 : Nat.card W = 16 := by
    rw [← S126L23b.card_ev5]
    have hbij : Function.Bijective
        (fun w : ↥W => (⟨d.β w, d.β_mem w w.2⟩ : {x // x ∈ ev5})) := by
      refine ⟨fun w₁ w₂ h => Subtype.ext (d.β_inj _ w₁.2 _ w₂.2 (congrArg Subtype.val h)), ?_⟩
      rintro ⟨x, hx⟩
      obtain ⟨w, hw, rfl⟩ := d.β_surj x hx
      exact ⟨⟨w, hw⟩, rfl⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hfixW : ∀ w ∈ W, w ∈ Subgroup.centralizer ({a₀} : Set G) ↔
      act5 (σ ⟨a₀, hAH ha₀A⟩) (d.β w) = d.β w := by
    intro w hw
    obtain ⟨haw, haβ⟩ := hactW a₀ ha₀A w hw
    rw [Subgroup.mem_centralizer_singleton_iff, ← haβ]
    constructor
    · intro h
      rw [show a₀ * w * a₀⁻¹ = w by rw [← h, mul_inv_cancel_right]]
    · intro h
      have := d.β_inj _ haw _ hw h
      calc w * a₀ = a₀ * w * a₀⁻¹ * a₀ := by rw [this]
        _ = a₀ * w := by group
  have hWC4 : Nat.card ↥(Subgroup.centralizer ({a₀} : Set G) ⊓ W) = 4 := by
    rw [← hcf]
    have hbij : Function.Bijective (fun w : ↥(Subgroup.centralizer ({a₀} : Set G) ⊓ W) =>
        (⟨d.β w, Finset.mem_filter.2 ⟨d.β_mem w w.2.2, (hfixW w w.2.2).1 w.2.1⟩⟩ :
          {x // x ∈ ev5.filter fun x => act5 (σ ⟨a₀, hAH ha₀A⟩) x = x})) := by
      refine ⟨fun w₁ w₂ h => Subtype.ext (d.β_inj _ w₁.2.2 _ w₂.2.2
        (congrArg Subtype.val h)), ?_⟩
      rintro ⟨x, hx⟩
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      obtain ⟨w, hw, rfl⟩ := d.β_surj x hx1
      exact ⟨⟨w, (hfixW w hw).2 hx2, hw⟩, rfl⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hne0 : ∀ C : Subgroup G, C.relIndex VH ≠ 0 := fun C h => by
    have := Subgroup.relIndex_mul_card (H := C) (K := VH)
    rw [h, zero_mul] at this
    exact (Nat.card_pos (α := ↥VH)).ne this
  have hrelW : (Subgroup.centralizer ({a₀} : Set G)).relIndex W = 4 := by
    have := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({a₀} : Set G)) (K := W)
    rw [hWC4, hW16] at this
    omega
  have h4le : 4 ≤ (Subgroup.centralizer ({a₀} : Set G)).relIndex VH := by
    rw [← hrelW]
    exact Subgroup.relIndex_le_of_le_right hWV (hne0 _)
  have hCAle : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a₀} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 ha₀A)
  have h4le' : 4 ≤ (Subgroup.centralizer (A : Set G)).relIndex VH :=
    h4le.trans (Subgroup.relIndex_le_of_le_left hCAle (hne0 _))
  have h2le : (Subgroup.centralizer (A : Set G)).relIndex VH ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (A : Set G)) (K := VH)
    rw [inf_comm] at h1
    have hpos : 0 < Nat.card ↥(VH ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
    nlinarith [hVHcard]
  omega

end S126L23e

theorem lemma12_6_23_of (h331 : Stmt3_3_1)
    (h3228 : Stmt3_2_2_eight) (h1222 : Stmt12_2_2) (h1227 : Stmt12_2_7) (h1228 : Stmt12_2_8)
    (h1229 : Stmt12_2_9) (h1232 : Cor12_3_2) (h1262 : Theorem12_6_2) (h1219 : Lemma12_6_19)
    (hS8 : FactS8ElemAbE8) : Lemma12_6_23 := by
  intro G _ _ T L V _ F hH
  have hZ := S126L23e.centralizer_eq_bot h331 h3228 h1222 h1227 h1228 h1229 h1232 h1262 h1219
    hS8 F hH
  exact ⟨hZ, S126L23d.part2 h1222 F hH hZ⟩

theorem lemma12_6_23_of_cert
    (h331 : Stmt3_3_1) (h3228 : Stmt3_2_2_eight) (h1222 : Stmt12_2_2) (h1227 : Stmt12_2_7)
    (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) (h1232 : Cor12_3_2) (h1262 : Theorem12_6_2)
    (h1219 : Lemma12_6_19) : Lemma12_6_23 :=
  lemma12_6_23_of h331 h3228 h1222 h1227 h1228 h1229 h1232 h1262 h1219
    S126L22F.factS8ElemAbE8_holds

end CFSG.Quasithin.H13
