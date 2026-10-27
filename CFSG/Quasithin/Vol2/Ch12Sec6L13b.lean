module

public import CFSG.Quasithin.Vol2.Ch12Sec6L13a
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch12Sec6L11d

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem mem_pCoreOf_iff {H : Subgroup G} (z : ↥H) :
    (z : G) ∈ pCoreOf 2 H ↔ z ∈ CFSG.pCore 2 ↥H := CFSG.mem_openPCoreOf_iff z

theorem inf_le_pCoreOf_or_le {K N : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hN : K ≤ Subgroup.normalizer (N : Set G)) :
    K ⊓ N ≤ pCoreOf 2 K ∨ K ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' : Subgroup ↥K := (K ⊓ N).subgroupOf K with hN'
  have hn : ∀ l ∈ K, ∀ x ∈ K ⊓ N, l * x * l⁻¹ ∈ K ⊓ N := fun l hl x hx =>
    ⟨K.mul_mem (K.mul_mem hl hx.1) (K.inv_mem hl), (Subgroup.mem_normalizer_iff.1 (hN hl) x).1 hx.2⟩
  have hN'n : N'.Normal := ⟨fun x hx l => by
    rw [hN', Subgroup.mem_subgroupOf] at hx ⊢
    exact hn l l.2 x hx⟩
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hmap : (N'.map φ).Normal := Subgroup.Normal.map hN'n φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map φ) with h | h
  · left
    intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥K) ∈ N' := hx
    have h1 : φ ⟨x, hx.1⟩ ∈ N'.map φ := ⟨_, hxN, rfl⟩
    rw [h, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (mem_pCoreOf_iff ⟨x, hx.1⟩).2 h1
  · right
    refine (Sec1216Lv.perfect_le_of_le_sup_two hK inf_le_left hn (pCoreOf_isPGroup 2 K)
      (pCoreOf_le 2 K) fun k hk => ?_).trans inf_le_right
    obtain ⟨n, hn', hnk⟩ := (h ▸ Subgroup.mem_top (φ ⟨k, hk⟩) : φ ⟨k, hk⟩ ∈ N'.map φ)
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
    have h2 : ((n : G))⁻¹ * k ∈ pCoreOf 2 K := (mem_pCoreOf_iff (n⁻¹ * ⟨k, hk⟩)).2 hnk
    have e : k = (n : G) * ((n : G)⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (show (n : G) ∈ K ⊓ N from hn') h2

theorem pCoreOf_Lv_le (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    pCoreOf 2 (Lv L v) ≤ Subgroup.centralizer (V : Set G) := by
  intro y hy
  have hyL : y ∈ L := Lv_le_L L v (pCoreOf_le 2 _ hy)
  have h1 := psi_pCore_eq_one h1222 F hH hv hβ (y := ⟨y, hyL⟩) hy
  have h2 : S126L19a.psi F hH ⟨y, hyL⟩ = 1 := Subtype.ext h1
  exact (S126L19a.psi_eq_one_iff F hH _).1 h2

omit [IsMulCommutative ↥V] in
theorem isPGroup_Lv_inf (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) (v : G) :
    IsPGroup 2 ↥(Lv L v ⊓ Subgroup.centralizer (V : Set G)) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, hn⟩ := S126L19a.isPGroup_ker h1222 hH ⟨⟨x, Lv_le_L L v hx.1⟩, hx.2⟩
  refine ⟨n, Subtype.ext ?_⟩
  have := congrArg (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) => ((z : ↥L) : G)) hn
  simpa using this

theorem Vv_ne_bot (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) : Vv L V v ≠ ⊥ := by
  intro h
  obtain ⟨u, huΔ, huV, hβu⟩ := exists_mem_Delta h1222 F hH hv hβ (a := 2) (b := 3) (by decide)
    (by decide) (by decide)
  have hu1 : u = 1 := by
    have := huΔ.2.1
    rw [h, Subgroup.mem_bot] at this
    exact this
  subst hu1
  have h1 : F.β ⟨1, huV⟩ = 1 := map_one F.β
  rw [h1] at hβu
  rcases (S126FE.mk_eq_one_iff _).1 hβu.symm with h2 | h2
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)

omit [IsMulCommutative ↥V] in
theorem Vv_le_comm (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) :
    Vv L V v ≤ ⁅Vv L V v, Lv L v⁆ :=
  le_comm_comm_of_perfect (perfectCore_perfect _) (V_le_normalizer_Lv h1222 hH hv)
    ((Lv_le_L L v).trans hH.hyp.irrPlus.2.2.1)

theorem charTwo_Lv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    CFSG.QuasithinUnique.CharTwo (Lv L v) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Lv L v ⊓ Subgroup.centralizer (pCoreOf 2 (Lv L v) : Set G) with hC
  have hLp : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
  have hCn : ∀ l ∈ Lv L v, ∀ x ∈ C, l * x * l⁻¹ ∈ C := fun l hl x hx =>
    (Subgroup.mem_normalizer_iff.1 (A4.mem_normalizer_inf (Subgroup.le_normalizer hl)
      (A4.mem_normalizer_centralizer (le_normalizer_pCoreOf 2 _ hl))) x).1 hx
  have hP2 := isPGroup_Lv_inf h1222 hH v
  have hCL : C ≤ Lv L v := inf_le_left
  set f := psiP F hH with hf
  set N : Subgroup (Equiv.Perm (Fin 8)) := (C.subgroupOf L).map f with hN
  have hNA : N ≤ A6s := by
    rintro _ ⟨c, hc, rfl⟩
    exact psiP_mem_A6s h1222 F hH hv hβ (show c ∈ (Lv L v).subgroupOf L from hCL hc)
  have hNn : ∀ a ∈ A6s, ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
    intro a ha n hn
    obtain ⟨l, hl, rfl⟩ := exists_Lv_of_A6s h1222 F hH hv hβ a ha
    obtain ⟨c, hc, rfl⟩ := hn
    exact ⟨l * c * l⁻¹, hCn _ hl _ hc, by rw [map_mul, map_mul, map_inv]⟩
  have hker : ∀ x : ↥L, f x = 1 → (x : G) ∈ Subgroup.centralizer (V : Set G) := fun x hx =>
    (S126L19a.psi_eq_one_iff F hH x).1 (Subtype.ext hx)
  rcases eq_bot_or_eq_of_normal hNA hNn with h | h
  ·
    have hCP : C ≤ Lv L v ⊓ Subgroup.centralizer (V : Set G) := by
      intro x hx
      have hxL : x ∈ L := Lv_le_L L v hx.1
      have h1 : f ⟨x, hxL⟩ ∈ N := ⟨⟨x, hxL⟩, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact ⟨hx.1, hker _ h1⟩
    exact le_pCoreOf_of_le_normalizer 2 hCL (fun l hl => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hCn l hl x, fun hx => ?_⟩
      have := hCn l⁻¹ ((Lv L v).inv_mem hl) _ hx
      rwa [show l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x by group] at this) (hP2.to_le hCP)
  ·
    exfalso
    have hle : Lv L v ≤ C ⊔ (Lv L v ⊓ Subgroup.centralizer (V : Set G)) := by
      intro x hx
      have hxL : x ∈ L := Lv_le_L L v hx
      have hfx : f ⟨x, hxL⟩ ∈ N := h ▸ psiP_mem_A6s h1222 F hH hv hβ
        (show (⟨x, hxL⟩ : ↥L) ∈ (Lv L v).subgroupOf L from hx)
      obtain ⟨c, hc, hcx⟩ := hfx
      have hc' : (c : G) ∈ C := hc
      have h1 : f (c⁻¹ * ⟨x, hxL⟩) = 1 := by rw [map_mul, map_inv, hcx, inv_mul_cancel]
      have h2 : (c : G)⁻¹ * x ∈ Lv L v ⊓ Subgroup.centralizer (V : Set G) :=
        ⟨(Lv L v).mul_mem ((Lv L v).inv_mem (hCL hc')) hx, hker _ h1⟩
      have e : x = (c : G) * ((c : G)⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hc' h2
    have hLC := Sec1216Lv.perfect_le_of_le_sup_two hLp hCL hCn hP2 inf_le_left hle
    have hcomm : ⁅Vv L V v, Lv L v⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlC : l ∈ Subgroup.centralizer (pCoreOf 2 (Lv L v) : Set G) := (hLC hl).2
      rw [Subgroup.mem_centralizer_iff] at hlC
      exact (hlC u (Vv_le_pCoreOf h1222 hH hv hu)).symm
    exact Vv_ne_bot h1222 F hH hv hβ (le_bot_iff.1 (hcomm ▸ Vv_le_comm h1222 hH hv))

theorem isXf_Lv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) : IsXf (Lv L v) := by
  have hLp : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  have hVΩ : Vv L V v ≤ omegaOneCenterOf (pCoreOf 2 (Lv L v)) := by
    intro u hu
    have huO := Vv_le_pCoreOf h1222 hH hv hu
    have huV := Vv_le_V hH v hu
    refine Subgroup.subset_closure ⟨⟨huO, ?_⟩, hVe.2 u huV⟩
    show u ∈ Subgroup.centralizer (pCoreOf 2 (Lv L v) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    exact ((Subgroup.mem_centralizer_iff.1 (pCoreOf_Lv_le h1222 F hH hv hβ ho)) u huV).symm
  have hne := Vv_ne_bot h1222 F hH hv hβ
  refine ⟨⟨fun h => hne ?_, (C2Nine.oTwoUpper_eq_of_perfect hLp).symm,
    charTwo_Lv h1222 F hH hv hβ⟩, fun h => hne ?_⟩
  · rw [Vv, h]
    exact Subgroup.commutator_bot_right _
  · exact le_bot_iff.1 ((Vv_le_comm h1222 hH hv).trans
      ((Subgroup.commutator_mono hVΩ le_rfl).trans h.le))

theorem charTwo_Kv (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S)
    (hD6 : ¬ CFSG.IsQuasisimple ↥Kv) : CFSG.QuasithinUnique.CharTwo Kv := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  have hs := isSimple_Kv h1222 h36 hC
  rcases inf_le_pCoreOf_or_le hK hs (N := Subgroup.centralizer (pCoreOf 2 Kv : Set G))
    (fun k hk => A4.mem_normalizer_centralizer (le_normalizer_pCoreOf 2 Kv hk)) with h | h
  · exact h
  · exfalso
    apply hD6
    have hperf : Group.IsPerfect ↥Kv := Subgroup.isPerfect_iff.mpr hK
    set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥Kv) with hφ
    have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
    have hcen : φ.ker ≤ Subgroup.center ↥Kv := by
      intro z hz
      rw [hφ, QuotientGroup.ker_mk'] at hz
      rw [Subgroup.mem_center_iff]
      intro k
      have hz' : (z : G) ∈ pCoreOf 2 Kv := (mem_pCoreOf_iff z).2 hz
      have := Subgroup.mem_centralizer_iff.1 (h k.2) _ hz'
      exact Subtype.ext this.symm
    obtain ⟨-, -, a, b, hab⟩ := hC.quasisimple
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have hnab : ∃ a b : ↥Kv ⧸ CFSG.pCore 2 ↥Kv, a * b ≠ b * a :=
      ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
    have hcz := RankThreeCoreUniqueness.Helpers.surjective_centerless_image_center_eq_kernel φ hφs
      hcen (RankThreeCoreUniqueness.Helpers.nonabelian_simple_center_eq_bot hnab)
    let e : ↥Kv ⧸ Subgroup.center ↥Kv ≃* ↥Kv ⧸ CFSG.pCore 2 ↥Kv :=
      (QuotientGroup.quotientMulEquivOfEq hcz).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
    refine ⟨hperf, (MulEquiv.isSimpleGroup_congr e).2 hs, ?_⟩
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨e.symm x, e.symm y, fun h => hxy (by
      have := congrArg e h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)⟩

theorem pCoreOf_KvS_le {F : Frame126 T L V} {v : G} {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) :
    pCoreOf 2 (Kv ⊔ S) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKS : Kv ⊔ S ≤ Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hsyl := A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS
  refine A4.le_of_normal_of_isSylowTwoOf hsyl (pCoreOf_le 2 _) ?_ (pCoreOf_isPGroup 2 _)
  exact Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreOf 2 _)

theorem a410Hyp (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hD2 : Lemma12_6_4_5) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hD6 : ¬ CFSG.IsQuasisimple ↥Kv) : A410Hyp (Lv L v) Kv S := by
  have hK : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  have hKS : Kv ⊔ S ≤ Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  obtain ⟨-, -, -, -, -, hOR, hRN, -⟩ := hD2 G T L V F v Kv S hC
  refine ⟨(isXf_Lv h1222 F hC.hyp hC.mem hC.coord).1,
    ⟨ne_bot_of_mem_cComp hC.cComp, (C2Nine.oTwoUpper_eq_of_perfect hK).symm,
      charTwo_Kv h1222 h36 hC hD6⟩,
    hC.lv_le, hC.sylow.1.trans hC.normal, A4.isSylowTwoOf_mono hC.sylow le_sup_right hKS,
    le_inf (pCoreOf_KvS_le hC) (hOR.trans hRN), ?_⟩
  exact A4.isSylowTwoOf_mono hC.sylowN (inf_le_inf_right _ le_sup_right)
    (inf_le_inf_right _ hKS)

theorem comm_Usec_ne_bot (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hD2 : Lemma12_6_4_5) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hD6 : ¬ CFSG.IsQuasisimple ↥Kv) : ⁅Usec Kv S, Kv⁆ ≠ ⊥ := by
  have hA := a410Hyp h1222 h36 hD2 hC hD6
  have hXf := a4_10_3 hA (isXf_Lv h1222 F hC.hyp hC.mem hC.coord)
  have hsub : IsSubnormal Kv (Kv ⊔ S) :=
    A4.subnormal_of_normal le_sup_left
      (Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hA.normalizes))
  exact (a4_9 hXf.1 hsub).mpr hXf.2

theorem pCoreOf_eq_centralizer (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (hD2 : Lemma12_6_4_5) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) (hD6 : ¬ CFSG.IsQuasisimple ↥Kv) :
    pCoreOf 2 (Kv ⊔ S) = (Kv ⊔ S) ⊓ Subgroup.centralizer (Usec Kv S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := Kv ⊔ S with hX
  set O := pCoreOf 2 X with hO
  set U := Usec Kv S with hU
  have hK : ⁅Kv, Kv⁆ = Kv := perfect_of_mem_cComp hC.cComp
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hUO : U ≤ Subgroup.centralizer (O : Set G) :=
    (A4.omegaOneCenterOf_le_centerOf O).trans (A4.centerOf_le_centralizer O)
  refine le_antisymm (le_inf (pCoreOf_le 2 X) (Subgroup.le_centralizer_iff.1 hUO)) ?_
  set D := X ⊓ Subgroup.centralizer (U : Set G) with hD
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := fun g hg =>
    A4.mem_normalizer_inf (Subgroup.le_normalizer hg) (A4.mem_normalizer_centralizer
      (A4.normalizer_le_normalizer_omegaOneCenterOf O (le_normalizer_pCoreOf 2 X hg)))
  rcases inf_le_pCoreOf_or_le hK (isSimple_Kv h1222 h36 hC)
    (fun k hk => hXD ((le_sup_left : Kv ≤ X) hk)) with h | h
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left hXD ?_
    rintro ⟨d, hd⟩
    have hd' : d ∈ (↑(Kv ⊔ S) : Set G) := hd.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Kv S hSK] at hd'
    obtain ⟨y, hy, t, ht, hyt⟩ := hd'
    obtain ⟨j, hj⟩ := hC.sylow.2.1 ⟨t, ht⟩
    have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
    obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hSK ht) (2 ^ j)
    have hdpow : d ^ 2 ^ j = y' := by
      rw [← hyt, hpow, hj', mul_one]
    have hmem : d ^ 2 ^ j ∈ Kv ⊓ D := ⟨hdpow ▸ hy', D.pow_mem hd _⟩
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 Kv ⟨_, h hmem⟩
    refine ⟨j + m, Subtype.ext ?_⟩
    show d ^ 2 ^ (j + m) = 1
    rw [pow_add, pow_mul]
    exact congrArg Subtype.val hm
  · exfalso
    apply comm_Usec_ne_bot h1222 h36 hD2 hC hD6
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.1 (h.trans inf_le_right)

end S126T2

end CFSG.Quasithin.H13
