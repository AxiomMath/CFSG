module

public import CFSG.Quasithin.H13.A5W1623a
public import CFSG.Quasithin.H13.A5W1622u
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2B

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.A5Model
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap
  mem_normalizer_perfectCore exists_inducedAut liftCore_perfect)

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem exists_slHom_plus (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hGA : GriessAllModelsStatement)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLv : S.Lv ≤ Subgroup.normalizer (K : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {m : ℕ} (hm4 : 4 ≤ m) (hm5 : m ≤ 5)
    (e : ↥(S.plus K) ≃* SpecialLinearGroup (Fin m) (ZMod 2)) :
    ∃ α : ↥K →* SpecialLinearGroup (Fin m) (ZMod 2), Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥K ∧
      ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card (ZMod 2) = 2 := Ln2P.card_zmod_two
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer (S.WK K : Set G) := hKH.trans hR.2.1
  set φ := InternalSec.autOnHom hKW with hφ
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hKW
  let e' : ↥(autOn K (S.WK K)) ≃* SpecialLinearGroup (Fin m) (ZMod 2) := e
  have hHK : S.HK K ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hLv) hT
  have hOC : pCoreOf 2 K ≤ Subgroup.centralizer (S.WK K : Set G) := by
    refine hR.2.2.2 _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (fun g hg => C1.mem_normalizer_blockQ (hHK hg)) fun d hd => ?_
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [h1]
    exact Subgroup.one_mem _
  have hNK : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro q hq
    rw [InternalSec.mem_ker_autOnHom]
    have hq' : q ∈ CFSG.Open.pCore 2 ↥K := by exact hq
    exact hOC ⟨q, hq', rfl⟩
  let α : ↥K →* SpecialLinearGroup (Fin m) (ZMod 2) := e'.toMonoidHom.comp φ
  have hαφ : ∀ k, α k = 1 ↔ φ k = 1 := fun k => MulEquiv.map_eq_one_iff e'
  have hαs : Function.Surjective α := e'.surjective.comp hφs
  have hKN : φ.ker ≤ CFSG.pCore 2 ↥K := by
    set N := CFSG.pCore 2 ↥K with hN
    set Kφ := φ.ker with hKφ
    have hNn : N.Normal := CFSG.pCore_normal
    have : Group.IsPerfect (↥K ⧸ N) := hq.1
    let e₂ : ↥(autOn K (S.WK K)) ≃* StatedProj (StatedSL m (ZMod 2)) :=
      e'.trans (slEquivStatedProj hK2 m)
    let q : ↥K ⧸ N →* StatedProj (StatedSL m (ZMod 2)) :=
      e₂.toMonoidHom.comp (QuotientGroup.lift N φ hNK)
    have hqmk : ∀ k : ↥K, q (k : ↥K ⧸ N) = e₂ (φ k) := fun k => rfl
    have hqs : Function.Surjective q := by
      intro y
      obtain ⟨k, hk⟩ := hφs (e₂.symm y)
      exact ⟨k, by rw [hqmk, hk, MulEquiv.apply_symm_apply]⟩
    have hker : ∀ k : ↥K, q (k : ↥K ⧸ N) = 1 ↔ k ∈ Kφ := fun k => by
      rw [hqmk]
      exact MulEquiv.map_eq_one_iff e₂
    have hqn : q.ker.Normal := MonoidHom.normal_ker q
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq q.ker with hc | htop
    ·
      have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hqs hc
      have hcard : Nat.card ↥q.ker ∣ 2 := by
        have h1 := Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier
          (StatedProj (StatedSL m (ZMod 2)))) (RankThree.PerfectCover.hopfLift q hqs hc)
        rw [hmap] at h1
        exact h1.trans (Ln2.card_hopfMultiplier_dvd_two hGA hK2 hm4 hm5)
      have hp : IsPGroup 2 ↥q.ker := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h1 | h1
        · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
        · exact IsPGroup.of_card (n := 1) (by rw [h1, pow_one])
      have hK2' : IsPGroup 2 ↥Kφ := by
        rintro ⟨k, hk⟩
        obtain ⟨a, ha⟩ := hp ⟨(k : ↥K ⧸ N), (hker k).mpr hk⟩
        have ha' : ((k ^ 2 ^ a : ↥K) : ↥K ⧸ N) = 1 := by
          have := congrArg Subtype.val ha
          simpa using this
        have hkN : k ^ 2 ^ a ∈ N := (QuotientGroup.eq_one_iff _).mp ha'
        obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hkN⟩
        refine ⟨a + b, Subtype.ext ?_⟩
        have hb' : (k ^ 2 ^ a) ^ 2 ^ b = 1 := by
          have := congrArg Subtype.val hb
          simpa using this
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [pow_add, pow_mul, hb']
      exact le_sSup ⟨MonoidHom.normal_ker φ, hK2'⟩
    · exfalso
      have htriv : ∀ k : ↥K, φ k = 1 := by
        intro k
        have hk : (k : ↥K ⧸ N) ∈ q.ker := htop ▸ Subgroup.mem_top _
        exact (hker k).mp hk
      obtain ⟨a, b, hab⟩ := sl_nonabelian_of_card_two hK2 (m := m) (by omega)
      obtain ⟨x, rfl⟩ := hαs a
      obtain ⟨y, rfl⟩ := hαs b
      apply hab
      have hx : α x = 1 := (hαφ x).mpr (htriv x)
      have hy : α y = 1 := (hαφ y).mpr (htriv y)
      rw [hx, hy]
  refine ⟨α, hαs, ?_, fun k => ?_⟩
  · ext k
    rw [MonoidHom.mem_ker, hαφ, ← MonoidHom.mem_ker]
    exact ⟨fun hk => hKN hk, fun hk => hNK hk⟩
  · rw [hαφ, ← MonoidHom.mem_ker, InternalSec.mem_ker_autOnHom]

theorem eq_parabolic_of_sl (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {K : Subgroup G} (hLvK : S.Lv ≤ K) {m : ℕ} (hm : 3 ≤ m)
    {α : ↥K →* SpecialLinearGroup (Fin m) (ZMod 2)}
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular m (ZMod 2)) :
    ∃ j, 1 ≤ j ∧ j < m ∧ ((S.Lv ⊔ (S.Tv ⊓ K)).subgroupOf K).map α =
      flagStabilizer m (ZMod 2) (Set.Icc 1 (m - 1) \ {j}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := S.Lv ⊔ (S.Tv ⊓ K) with hXdef
  set P := (X.subgroupOf K).map α with hPdef
  have hXK : X ≤ K := sup_le hLvK inf_le_right
  have hTvK : S.Tv ⊓ K ≤ Subgroup.normalizer (S.Lv : Set G) :=
    inf_le_left.trans S.Tv_le_normalizer_Lv
  have hUP : unitriangular m (ZMod 2) ≤ P := by
    rw [← hmapU]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  have hsylU : IsSylowTwoOf (unitriangular m (ZMod 2)) ⊤ :=
    SzN2.isSylowTwoOf_unitriangular (by omega)
  have hT2 : IsPGroup 2 ↥(S.Tv ⊓ K) := (S.isSylowTwoOf_Tv h1222 h517).2.1.to_le inf_le_left
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hT2
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp S.isPGroup_LvQ
  have hLv : Nat.card S.Lv = S.LvQ.relIndex S.Lv * 2 ^ a := by
    rw [← ha, ← Subgroup.relIndex_mul_card (H := S.LvQ) (K := S.Lv),
      inf_eq_left.mpr S.LvQ_le_Lv]
  have hX : Nat.card X ∣ S.LvQ.relIndex S.Lv * 2 ^ (a + b) := by
    have h1 := Ln2P.card_sup_dvd_mul S.Lv (S.Tv ⊓ K) hTvK
    rw [hLv, hb, mul_assoc, ← pow_add] at h1
    exact h1
  have hPc : Nat.card P ∣ Nat.card X := by
    have h1 := Subgroup.card_map_dvd (H := X.subgroupOf K) α
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv] at h1
  have hodd : ¬ 2 ∣ (unitriangular m (ZMod 2)).relIndex P := fun h2 => by
    apply hsylU.2.2
    show 2 ∣ (unitriangular m (ZMod 2)).relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hUP]
    exact Dvd.dvd.mul_right h2 _
  have hidx : (unitriangular m (ZMod 2)).relIndex P ∣ S.LvQ.relIndex S.Lv := by
    have h1 : (unitriangular m (ZMod 2)).relIndex P ∣ Nat.card P := by
      rw [← Subgroup.relIndex_mul_card (H := unitriangular m (ZMod 2)) (K := P)]
      exact Dvd.intro _ rfl
    have h2 := h1.trans (hPc.trans hX)
    have hco : Nat.Coprime ((unitriangular m (ZMod 2)).relIndex P) (2 ^ (a + b)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    exact hco.dvd_of_dvd_mul_right h2
  have hpos : 0 < S.LvQ.relIndex S.Lv := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h3 : (unitriangular m (ZMod 2)).relIndex P ≤ 3 :=
    (Nat.le_of_dvd hpos hidx).trans S.relIndex_LvQ_le
  rcases eq_or_eq_parabolic hUP h3 with hPU | ⟨j, ⟨hj, hjm, hPj⟩, -⟩
  ·
    exfalso
    apply S.not_Lv_le_centralizer_z
    have hzW : S.z ∈ S.WK K := le_conjClosure _ _ (Subgroup.mem_zpowers _)
    refine le_trans ?_ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzW))
    show oTwoRes (L ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤ _
    rw [oTwoRes, Subgroup.closure_le]
    rintro x ⟨hxX, m', hm', hxm⟩
    have hxLv : x ∈ S.Lv := Subgroup.subset_closure ⟨hxX, m', hm', hxm⟩
    have hxK : x ∈ K := hLvK hxLv
    have hxP : α ⟨x, hxK⟩ ∈ unitriangular m (ZMod 2) := by
      rw [← hPU]
      exact ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hxLv), rfl⟩
    obtain ⟨e, he⟩ := hsylU.2.1 ⟨_, hxP⟩
    have h1 : α ⟨x, hxK⟩ ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have h2 : α ⟨x, hxK⟩ ^ m' = 1 := by
      rw [← map_pow]
      have : (⟨x, hxK⟩ : ↥K) ^ m' = 1 := Subtype.ext (by simpa using hxm)
      rw [this, map_one]
    have h3 : α ⟨x, hxK⟩ = 1 := by
      have h5 := Ln2P.mem_of_pow_two_pow_mem (N := ⊥) hm' h2 (by rw [h1]; exact Subgroup.one_mem _)
      exact Subgroup.mem_bot.mp h5
    exact (hαC ⟨x, hxK⟩).mp h3
  · exact ⟨j, hj, hjm, hPj⟩

theorem inner_of_sl {K : Subgroup G} (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {m : ℕ}
    (hm4 : 4 ≤ m) (hm5 : m ≤ 5) {α : ↥K →* SpecialLinearGroup (Fin m) (ZMod 2)}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥K)
    (hαC : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G))
    (hmapU : ((S.Tv ⊓ K).subgroupOf K).map α = unitriangular m (ZMod 2)) {j : ℕ} (hj : 1 ≤ j)
    (hjm : j < m) (hP : ((S.Lv ⊔ (S.Tv ⊓ K)).subgroupOf K).map α =
      flagStabilizer m (ZMod 2) (Set.Icc 1 (m - 1) \ {j}))
    (hEnd : m = 4 → ∀ t ∈ S.Tv, ∀ Y : Subgroup G, Y ≤ K → S.Tv ⊓ K ≤ Y →
      K ⊓ Subgroup.centralizer (S.WK K : Set G) ≤ Y → t ∈ Subgroup.normalizer (Y : Set G)) :
    ∀ t ∈ S.Tv, ∃ u ∈ unitriangular m (ZMod 2), ∀ (l : ↥K) (h : t * l * t⁻¹ ∈ K),
      α ⟨t * l * t⁻¹, h⟩ = u * α l * u⁻¹ := by
  intro t ht
  obtain ⟨ψ, hψ⟩ := exists_inducedAut hαs hαk (hT ht)
  have hTK : t ∈ Subgroup.normalizer ((S.Tv ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hT ht⟩
  have hU : ∀ u ∈ unitriangular m (ZMod 2), ψ u ∈ unitriangular m (ZMod 2) := by
    intro u hu
    rw [← hmapU] at hu ⊢
    obtain ⟨l, hl, rfl⟩ := hu
    rw [hψ]
    refine ⟨_, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp hTK l).mp (Subgroup.mem_subgroupOf.mp hl))
  rcases Ln2P.mulAut_cases (by omega) ψ hU with ⟨u, hu, hcu⟩ | ⟨u, hu, hgu⟩
  · exact ⟨u, hu, fun l h => by rw [← hcu, hψ]⟩
  · exfalso
    have htX : t ∈ Subgroup.normalizer ((S.Lv ⊔ (S.Tv ⊓ K) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (S.Tv_le_normalizer_Lv ht),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hTK]
    have hM : ∀ g ∈ flagStabilizer m (ZMod 2) (Set.Icc 1 (m - 1) \ {j}),
        ψ g ∈ flagStabilizer m (ZMod 2) (Set.Icc 1 (m - 1) \ {j}) := by
      intro g hg
      rw [← hP] at hg ⊢
      obtain ⟨l, hl, rfl⟩ := hg
      rw [hψ]
      refine ⟨_, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp htX l).mp (Subgroup.mem_subgroupOf.mp hl))
    have hmj := Ln2P.eq_of_graph_of_map_le hj hjm hu hgu hM
    have hm4' : m = 4 := by omega
    set Y := liftPre α (flagStabilizer m (ZMod 2) {1}) with hYdef
    have hYK : Y ≤ K := L3316.liftPre_le α _
    have hTY : S.Tv ⊓ K ≤ Y := by
      intro x hx
      refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
      show α ⟨x, hx.2⟩ ∈ flagStabilizer m (ZMod 2) {1}
      apply unitriangular_le_flagStabilizer
      rw [← hmapU]
      exact ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hCY : K ⊓ Subgroup.centralizer (S.WK K : Set G) ≤ Y := by
      intro x hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      show α ⟨x, hx.1⟩ ∈ flagStabilizer m (ZMod 2) {1}
      rw [(hαC ⟨x, hx.1⟩).mpr hx.2]
      exact Subgroup.one_mem _
    have htY := hEnd hm4' t ht Y hYK hTY hCY
    apply Ln2P.graphAut_not_map_stab_one (n := m) (by omega)
    intro g hg
    obtain ⟨l, hl⟩ := hαs (u⁻¹ * g * u)
    have huQ : u ∈ flagStabilizer m (ZMod 2) {1} := unitriangular_le_flagStabilizer _ hu
    have hlY : (l : G) ∈ Y := by
      refine ⟨l, ?_, rfl⟩
      show α l ∈ flagStabilizer m (ZMod 2) {1}
      rw [hl]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ huQ) hg) huQ
    have hlK : t * (l : G) * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hT ht) l).mp l.2
    obtain ⟨l', hl', hl'e⟩ := (Subgroup.mem_normalizer_iff.mp htY l).mp hlY
    have hl'eq : l' = ⟨t * l * t⁻¹, hlK⟩ := Subtype.ext hl'e
    rw [hl'eq] at hl'
    have h2 : α ⟨t * l * t⁻¹, hlK⟩ = graphAut m g := by
      rw [← hψ, hgu, hl, show u * (u⁻¹ * g * u) * u⁻¹ = g by group]
    rw [← h2]
    exact hl'

end Setting

end CFSG.Quasithin.H13.A5
