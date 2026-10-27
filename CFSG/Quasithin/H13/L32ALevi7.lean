module

public import CFSG.Quasithin.H13.L32ALevi5

public section

namespace CFSG.Quasithin.H13.L32A.C.Levi

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

variable {G : Type} [Group G]

@[expose] def fixSub (N : Subgroup G) (a : G) (X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (N : Set G)) : Subgroup G where
  carrier := {x | x ∈ X ∧ x * a * x⁻¹ * a⁻¹ ∈ N}
  mul_mem' := by
    rintro x y ⟨hx, hxa⟩ ⟨hy, hya⟩
    refine ⟨X.mul_mem hx hy, ?_⟩
    have h1 : x * (y * a * y⁻¹ * a⁻¹) * x⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hX hx) _).mp hya
    have e : x * y * a * (x * y)⁻¹ * a⁻¹ = x * (y * a * y⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹ * a⁻¹) := by
      group
    rw [e]
    exact N.mul_mem h1 hxa
  one_mem' := ⟨X.one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxa⟩
    refine ⟨X.inv_mem hx, ?_⟩
    have h1 : x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hX (X.inv_mem hx)) _).mp (N.inv_mem hxa)
    have e : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact h1

structure HSide (T L V H K V₁ : Subgroup G) (πK : ↥K →* Lin.SLn 4) (a c x : G) : Prop where
  hKH : K ≤ H
  hTH : T ≤ H
  hKn : H ≤ Subgroup.normalizer (K : Set G)
  hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)
  hπs : Function.Surjective πK
  hkerK : ∀ k : ↥K, πK k = 1 ↔ (k : G) ∈ pCoreOf 2 K
  hD : (T.subgroupOf K).map πK = unitriangular 4 (ZMod 2)
  hPar : unitriangular 4 (ZMod 2) ⊔ ((l1 T L V).subgroupOf K).map πK = Lin.par 4 2
  hl1K : l1 T L V ≤ K
  hdec : ∀ h ∈ H, ∃ k ∈ K, ∃ t ∈ T, h = k * t
  hcent : ∀ h ∈ H, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 K) → h ∈ pCoreOf 2 H
  hodd : ∃ t ∈ T, ¬ ∃ k ∈ K, ∀ k' ∈ K, (k⁻¹ * t) * k' * (k⁻¹ * t)⁻¹ * k'⁻¹ ∈ pCoreOf 2 K
  hOK : pCoreOf 2 K ≤ pCoreOf 2 H
  hOT : pCoreOf 2 H ≤ T
  hU : IsElemAbelian 2 (conjClosure V H)
  hV₁U : V₁ ≤ conjClosure V H
  hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)
  hO : ∀ h ∈ pCoreOf 2 H, ∀ u ∈ conjClosure V H, h * u * h⁻¹ * u⁻¹ ∈ V₁
  ha : a ∈ conjClosure V H
  haV₁ : a ∉ V₁
  hTa : ∀ t ∈ T, t * a * t⁻¹ * a⁻¹ ∈ V₁
  hx : x ∈ l1 T L V
  hc : c ∈ conjClosure V H
  hxa : x * a * x⁻¹ = c
  hxc : x * c * x⁻¹ = a * c
  hca : c * a⁻¹ ∉ V₁

namespace HSide

variable {T L V H K V₁ : Subgroup G} {πK : ↥K →* Lin.SLn 4} {a c x : G}
  (C : HSide T L V H K V₁ πK a c x)
include C

@[expose] noncomputable def β : ↥H →* MulAut (Lin.SLn 4) :=
  indHom πK C.hπs C.hkerK C.hKn C.hHN

theorem β_apply (h : ↥H) (k : ↥K) : C.β h (πK k) = πK (conjK (C.hKn h.2) k) :=
  indHom_apply πK C.hπs C.hkerK C.hKn C.hHN h k

theorem β_K {k : G} (hk : k ∈ K) : C.β ⟨k, C.hKH hk⟩ = autOf (πK ⟨k, hk⟩) false := by
  ext g : 1
  obtain ⟨k', rfl⟩ := C.hπs g
  rw [C.β_apply, autOf_apply]
  have e : conjK (C.hKn (C.hKH hk)) k' = ⟨k, hk⟩ * k' * ⟨k, hk⟩⁻¹ := Subtype.ext (by
    rw [conjK_apply]
    rfl)
  rw [e, map_mul, map_mul, map_inv]
  rfl

theorem mem_T_K {t : G} (htT : t ∈ T) (htK : t ∈ K) :
    πK ⟨t, htK⟩ ∈ unitriangular 4 (ZMod 2) := by
  rw [← C.hD]
  exact ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.mpr htT, rfl⟩

theorem exists_T_K {u : Lin.SLn 4} (hu : u ∈ unitriangular 4 (ZMod 2)) :
    ∃ t ∈ T, ∃ ht : t ∈ K, πK ⟨t, ht⟩ = u := by
  rw [← C.hD] at hu
  obtain ⟨k, hk, rfl⟩ := hu
  exact ⟨k, Subgroup.mem_subgroupOf.mp hk, k.2, rfl⟩

theorem β_T_map {t : G} (ht : t ∈ T) {w : Lin.SLn 4} (hw : w ∈ unitriangular 4 (ZMod 2)) :
    C.β ⟨t, C.hTH ht⟩ w ∈ unitriangular 4 (ZMod 2) := by
  obtain ⟨s, hsT, hsK, rfl⟩ := C.exists_T_K hw
  rw [C.β_apply]
  apply C.mem_T_K
  show t * s * t⁻¹ ∈ T
  exact T.mul_mem (T.mul_mem ht hsT) (T.inv_mem ht)

theorem β_T {t : G} (ht : t ∈ T) :
    ∃ u ∈ unitriangular 4 (ZMod 2), ∃ e, C.β ⟨t, C.hTH ht⟩ = autOf u e := by
  obtain ⟨u, e, hue⟩ := exists_autOf (C.β ⟨t, C.hTH ht⟩)
  refine ⟨u, ?_, e, hue⟩
  rw [← BinaryParabolic.upperTriangular_eq_unitriangular, ← normalizer_unitriangular]
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  have hg : gamE e w ∈ unitriangular 4 (ZMod 2) := by
    cases e
    · exact hw
    · exact BinaryParabolic.graphFun_mem_unitriangular hw
  have := C.β_T_map ht hg
  rwa [hue, autOf_apply, gamE_gamE, Bool.xor_self, show gamE false w = w from rfl] at this

theorem comm_of_β {h : ↥H} (hh : C.β h = 1) :
    ∀ k ∈ K, (h : G) * k * (h : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  intro k hk
  have h1 := congrArg (fun α : MulAut (Lin.SLn 4) => α (πK ⟨k, hk⟩)) hh
  simp only [MulAut.one_apply] at h1
  rw [C.β_apply] at h1
  have h2 : πK (conjK (C.hKn h.2) ⟨k, hk⟩ * ⟨k, hk⟩⁻¹) = 1 := by
    rw [map_mul, h1, map_inv, mul_inv_cancel]
  have := (C.hkerK _).mp h2
  simpa [conjK_apply] using this

theorem β_ker {h : ↥H} (hh : C.β h = 1) : (h : G) ∈ pCoreOf 2 H :=
  C.hcent h h.2 (C.comm_of_β hh)

theorem eq_of_piK {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) (he : πK ⟨k, hk⟩ = πK ⟨k', hk'⟩) :
    k'⁻¹ * k ∈ pCoreOf 2 H := by
  apply C.hOK
  have h1 : πK (⟨k', hk'⟩⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  exact (C.hkerK _).mp h1

theorem lam_mem : πK ⟨x, C.hl1K C.hx⟩ ∈ Lin.par 4 2 := by
  rw [← C.hPar]
  exact Subgroup.mem_sup_right ⟨⟨x, C.hl1K C.hx⟩, Subgroup.mem_subgroupOf.mpr C.hx, rfl⟩

theorem fix_of_piK_mem {k : G} (hk : k ∈ K) (hu : πK ⟨k, hk⟩ ∈ unitriangular 4 (ZMod 2)) :
    k ∈ T := by
  obtain ⟨t, htT, htK, he⟩ := C.exists_T_K hu
  have := C.hOT (C.eq_of_piK hk htK he.symm)
  have e : k = t * (t⁻¹ * k) := by group
  rw [e]
  exact T.mul_mem htT this

theorem lam_notMem : πK ⟨x, C.hl1K C.hx⟩ ∉ unitriangular 4 (ZMod 2) := by
  intro hu
  apply C.hca
  have := C.hTa x (C.fix_of_piK_mem (C.hl1K C.hx) hu)
  rwa [C.hxa] at this

theorem c_notMem : c ∉ V₁ := fun h => C.haV₁ (by
  have := (Subgroup.mem_normalizer_iff.mp (C.hHV₁ (C.hKH (C.hl1K C.hx))) a).mpr
  rw [C.hxa] at this
  exact this h)

theorem lam2_notMem : πK ⟨x, C.hl1K C.hx⟩ ^ 2 ∉ unitriangular 4 (ZMod 2) := by
  intro hu
  have hx2 : x * x ∈ K := K.mul_mem (C.hl1K C.hx) (C.hl1K C.hx)
  have hT : x * x ∈ T := C.fix_of_piK_mem hx2 (by
    rw [show (⟨x * x, hx2⟩ : ↥K) = ⟨x, C.hl1K C.hx⟩ ^ 2 from Subtype.ext (pow_two x).symm,
      map_pow]
    exact hu)
  have h1 := C.hTa _ hT
  have := C.hU.1
  have e : x * x * a * (x * x)⁻¹ * a⁻¹ = c := by
    have h2 : x * x * a * (x * x)⁻¹ = a * c := by
      rw [show x * x * a * (x * x)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ by group, C.hxa, C.hxc]
    rw [h2, mul_assoc, setLike_mul_comm C.hc (inv_mem C.ha), ← mul_assoc, mul_inv_cancel,
      one_mul]
  rw [e] at h1
  exact C.c_notMem h1

theorem lam_cases :
    (R2⁻¹ * πK ⟨x, C.hl1K C.hx⟩ ∈ unitriangular 4 (ZMod 2) ∧
      M2⁻¹ * πK ⟨x, C.hl1K C.hx⟩ ^ 2 ∈ unitriangular 4 (ZMod 2)) ∨
    (M2⁻¹ * πK ⟨x, C.hl1K C.hx⟩ ∈ unitriangular 4 (ZMod 2) ∧
      R2⁻¹ * πK ⟨x, C.hl1K C.hx⟩ ^ 2 ∈ unitriangular 4 (ZMod 2)) := by
  have hn := C.lam_notMem
  have hm := C.lam_mem
  have hn2 := C.lam2_notMem
  generalize πK ⟨x, C.hl1K C.hx⟩ = l at hn hm hn2 ⊢
  have hsame : ∀ w : Lin.SLn 4, w⁻¹ * l ∈ unitriangular 4 (ZMod 2) →
      w⁻¹ * l ^ 2 ∉ unitriangular 4 (ZMod 2) := fun w h1 h2 => hn (by
    have := mul_mem (inv_mem h1) h2
    have e : (w⁻¹ * l)⁻¹ * (w⁻¹ * l ^ 2) = l := by group
    rwa [e] at this)
  rcases par_cases hm with h | h | h
  · exact absurd h hn
  · left
    refine ⟨h, ?_⟩
    rcases par_cases (pow_mem hm 2) with h' | h' | h'
    · exact absurd h' hn2
    · exact absurd h' (hsame _ h)
    · exact h'
  · right
    refine ⟨h, ?_⟩
    rcases par_cases (pow_mem hm 2) with h' | h' | h'
    · exact absurd h' hn2
    · exact h'
    · exact absurd h' (hsame _ h)

theorem U_le_map {X : Subgroup G} (hTX : T ⊓ K ≤ X) :
    unitriangular 4 (ZMod 2) ≤ (X.subgroupOf K).map πK := by
  intro u hu
  obtain ⟨t, htT, htK, rfl⟩ := C.exists_T_K hu
  exact ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.mpr (hTX ⟨htT, htK⟩), rfl⟩

theorem r2_notMem {Y I : Subgroup G} (hYK : Y ≤ K) (hHI : H ≤ Subgroup.normalizer (I : Set G))
    (hV₁I : V₁ ≤ I) (hYI : ∀ y ∈ Y, y * a * y⁻¹ * a⁻¹ ∈ I) (hxI : c * a⁻¹ ∉ I) :
    reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) ∉
      ((Y ⊔ (T ⊓ K)).subgroupOf K).map πK := by
  intro hr
  set F := fixSub I a H hHI
  have hYF : Y ⊔ (T ⊓ K) ≤ F := sup_le (fun y hy => ⟨C.hKH (hYK hy), hYI y hy⟩)
    (fun t ht => ⟨C.hTH ht.1, hV₁I (C.hTa t ht.1)⟩)
  have hUA : unitriangular 4 (ZMod 2) ≤ ((Y ⊔ (T ⊓ K)).subgroupOf K).map πK := by
    intro u hu
    obtain ⟨t, htT, htK, rfl⟩ := C.exists_T_K hu
    exact ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ⟨htT, htK⟩), rfl⟩
  have hM : Lin.par 4 2 ≤ ((Y ⊔ (T ⊓ K)).subgroupOf K).map πK := by
    rw [Lin.par, BinaryParabolic.parabolic_eq_closure (j := 2) (by norm_num) (by norm_num),
      Subgroup.closure_le]
    rintro g (hg | hg)
    · exact hUA hg
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hr
  obtain ⟨k, hk, he⟩ := hM C.lam_mem
  have hkF : (k : G) ∈ F := hYF (Subgroup.mem_subgroupOf.mp hk)
  have ho := C.eq_of_piK (C.hl1K C.hx) k.2 he.symm
  have hoF : (k : G)⁻¹ * x ∈ F := ⟨C.hKH (K.mul_mem (K.inv_mem k.2) (C.hl1K C.hx)),
    hV₁I (by
      have := C.hO _ ho a C.ha
      exact this)⟩
  have hxF : x ∈ F := by
    have := F.mul_mem hkF hoF
    rwa [mul_inv_cancel_left] at this
  apply hxI
  have := hxF.2
  rwa [C.hxa] at this

omit C in
theorem le_stab_of_r2 {A : Subgroup (Lin.SLn 4)} (hUA : unitriangular 4 (ZMod 2) ≤ A)
    (hr : reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) ∉ A) :
    A ≤ stabilizer (flagSpace 4 (ZMod 2) 2) := by
  obtain ⟨hA, -⟩ := borel_overgroups A
    (BinaryParabolic.upperTriangular_eq_unitriangular ▸ hUA)
  have h2 : 2 ∈ borelOvergroupCuts A := ⟨by norm_num, by norm_num, hr⟩
  intro g hg
  rw [hA] at hg
  exact mem_flagStabilizer.mp hg 2 h2

omit C in
theorem stab_le_of {A : Subgroup (Lin.SLn 4)} (hUA : unitriangular 4 (ZMod 2) ≤ A)
    (h1 : reflection 4 (ZMod 2) 1 (by norm_num) (by norm_num) ∈ A)
    (h3 : reflection 4 (ZMod 2) 3 (by norm_num) (by norm_num) ∈ A) :
    stabilizer (flagSpace 4 (ZMod 2) 2) ≤ A := by
  intro g hg
  have hg' : g ∈ flagStabilizer 4 (ZMod 2) {2} :=
    mem_flagStabilizer.mpr fun i hi => by rw [Set.mem_singleton_iff.mp hi]; exact hg
  rw [(subflag_stabilizer_generation (K := ZMod 2) (n := 4) {2}).1] at hg'
  refine (Subgroup.closure_le A).mpr ?_ hg'
  rintro y (hy | ⟨j, hj, hjn, hj2, rfl⟩)
  · exact hUA (BinaryParabolic.upperTriangular_eq_unitriangular ▸ hy)
  · have hj2' : j ≠ 2 := hj2
    interval_cases j
    · exact h1
    · exact absurd rfl hj2'
    · exact h3

theorem cent_le_T {Y : Subgroup G} (hYK : Y ≤ K)
    (hYP : ((Y ⊔ (T ⊓ K)).subgroupOf K).map πK ≤ stabilizer (flagSpace 4 (ZMod 2) 2))
    (hbad : ∃ y ∈ Y, y * a * y⁻¹ * a⁻¹ ∉ V₁) :
    ∀ h ∈ H, h * a * h⁻¹ * a⁻¹ ∈ V₁ → h ∈ T := by
  set F := fixSub V₁ a H C.hHV₁ with hF
  set A := ((F ⊓ K).subgroupOf K).map πK with hA
  have hTF : T ≤ F := fun t ht => ⟨C.hTH ht, C.hTa t ht⟩
  have hOF : pCoreOf 2 H ≤ F := fun o ho =>
    ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H ho, C.hO o ho a C.ha⟩
  have hUA : unitriangular 4 (ZMod 2) ≤ A := by
    intro u hu
    obtain ⟨t, htT, htK, rfl⟩ := C.exists_T_K hu
    exact ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.mpr ⟨hTF htT, htK⟩, rfl⟩
  have hlift : ∀ k (hk : k ∈ K), πK ⟨k, hk⟩ ∈ A → k ∈ F := by
    rintro k hk ⟨k', hk', he⟩
    have h1 := C.eq_of_piK hk k'.2 he.symm
    have hk'F : (k' : G) ∈ F := (Subgroup.mem_subgroupOf.mp hk').1
    have := F.mul_mem hk'F (hOF h1)
    rwa [mul_inv_cancel_left] at this
  obtain ⟨t₀, ht₀, hout⟩ := C.hodd
  obtain ⟨u₀, hu₀, e₀, he₀⟩ := C.β_T ht₀
  have he₀1 : e₀ = true := by
    cases e₀
    · exfalso
      apply hout
      obtain ⟨s, hsT, hsK, hsu⟩ := C.exists_T_K hu₀
      refine ⟨s, hsK, fun k' hk' => ?_⟩
      have hβ : C.β (⟨s, C.hKH hsK⟩⁻¹ * ⟨t₀, C.hTH ht₀⟩) = 1 := by
        rw [map_mul, map_inv, C.β_K hsK, hsu, he₀, inv_mul_cancel]
      exact C.comm_of_β hβ k' hk'
    · rfl
  subst he₀1
  have hinv : ∀ g ∈ A, u₀ * BinaryParabolic.graphFun g * u₀⁻¹ ∈ A := by
    rintro _ ⟨k, hk, rfl⟩
    have hkF := (Subgroup.mem_subgroupOf.mp hk).1
    have e1 : u₀ * BinaryParabolic.graphFun (πK k) * u₀⁻¹ = C.β ⟨t₀, C.hTH ht₀⟩ (πK k) := by
      rw [he₀, autOf_apply]
      rfl
    rw [e1, C.β_apply]
    refine ⟨conjK (C.hKn (C.hTH ht₀)) k, Subgroup.mem_subgroupOf.mpr ⟨?_, (conjK _ k).2⟩, rfl⟩
    rw [conjK_apply]
    exact F.mul_mem (F.mul_mem (hTF ht₀) hkF) (F.inv_mem (hTF ht₀))
  have hswap : ∀ j (hj : 1 ≤ j) (hjn : j < 4), Lin.par 4 j ≤ A → Lin.par 4 (4 - j) ≤ A := by
    intro j hj hjn hM g hg
    have hm : BinaryParabolic.graphFun (u₀⁻¹ * g * u₀) ∈ Lin.par 4 j := by
      have h1 : u₀⁻¹ * g * u₀ ∈ Lin.par 4 (4 - j) := by
        have hu' := BinaryParabolic.unitriangular_le_flagStabilizer
          (Set.Icc 1 (4 - 1) \ {4 - j}) hu₀
        exact mul_mem (mul_mem (inv_mem hu') hg) hu'
      have h2 := BinaryParabolic.map_graphAut_parabolic (n := 4) (j := 4 - j) (by omega)
        (by omega)
      rw [show 4 - (4 - j) = j by omega] at h2
      rw [← BinaryParabolic.graphAut_apply, Lin.par, ← h2]
      exact ⟨_, h1, rfl⟩
    have := hinv _ (hM hm)
    rwa [BinaryParabolic.graphFun_graphFun, mul_assoc, mul_assoc, mul_inv_cancel, mul_one,
      ← mul_assoc, mul_inv_cancel, one_mul] at this
  have hrefl : ∀ j (hj : 1 ≤ j) (hjn : j < 4), reflection 4 (ZMod 2) j hj hjn ∈ A →
      Lin.par 4 j ≤ A := by
    intro j hj hjn hr
    rw [Lin.par, BinaryParabolic.parabolic_eq_closure hj hjn, Subgroup.closure_le]
    rintro g (hg | hg)
    · exact hUA hg
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hr
  have hY : ∀ j (hj : 1 ≤ j) (hjn : j < 4), j ≠ 2 → reflection 4 (ZMod 2) j hj hjn ∉ A := by
    intro j hj hjn hj2 hr
    have hMj := hrefl j hj hjn hr
    have hMj' := hswap j hj hjn hMj
    have r1 : reflection 4 (ZMod 2) 1 (by norm_num) (by norm_num) ∈ A := by
      rcases (by omega : j = 1 ∨ j = 3) with rfl | rfl
      · exact hMj (BinaryParabolic.reflection_mem_parabolic _ _)
      · exact hMj' (BinaryParabolic.reflection_mem_parabolic _ _)
    have r3 : reflection 4 (ZMod 2) 3 (by norm_num) (by norm_num) ∈ A := by
      rcases (by omega : j = 1 ∨ j = 3) with rfl | rfl
      · exact hMj' (BinaryParabolic.reflection_mem_parabolic _ _)
      · exact hMj (BinaryParabolic.reflection_mem_parabolic _ _)
    obtain ⟨y, hyY, hya⟩ := hbad
    apply hya
    have hyA : πK ⟨y, hYK hyY⟩ ∈ A := stab_le_of hUA r1 r3
      (hYP ⟨⟨y, hYK hyY⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hyY), rfl⟩)
    exact (hlift y (hYK hyY) hyA).2
  have h2 : reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) ∉ A := by
    intro hr
    have hM := hrefl 2 (by norm_num) (by norm_num) hr
    apply C.hca
    have := (hlift x (C.hl1K C.hx) (hM C.lam_mem)).2
    rwa [C.hxa] at this
  have hAU : A = unitriangular 4 (ZMod 2) := by
    obtain ⟨hAeq, -⟩ := borel_overgroups A
      (BinaryParabolic.upperTriangular_eq_unitriangular ▸ hUA)
    have hcuts : borelOvergroupCuts A = Set.Icc 1 (4 - 1) := by
      ext i
      constructor
      · rintro ⟨hi, hin, -⟩
        exact ⟨hi, by omega⟩
      · rintro ⟨hi, hin⟩
        refine ⟨hi, by omega, ?_⟩
        rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
        · exact hY 1 _ _ (by norm_num)
        · exact h2
        · exact hY 3 _ _ (by norm_num)
    rw [hAeq, hcuts, BinaryParabolic.flagStabilizer_Icc]
  intro h hh hfix
  obtain ⟨k, hk, t, ht, rfl⟩ := C.hdec h hh
  have hkF : k ∈ F := by
    have := F.mul_mem (show k * t ∈ F from ⟨hh, hfix⟩) (F.inv_mem (hTF ht))
    rwa [mul_inv_cancel_right] at this
  have hkA : πK ⟨k, hk⟩ ∈ A := ⟨⟨k, hk⟩, Subgroup.mem_subgroupOf.mpr ⟨hkF, hk⟩, rfl⟩
  rw [hAU] at hkA
  exact T.mul_mem (C.fix_of_piK_mem hk hkA) ht

end HSide

end CFSG.Quasithin.H13.L32A.C.Levi
