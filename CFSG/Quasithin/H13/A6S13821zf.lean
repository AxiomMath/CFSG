module

public import CFSG.Quasithin.H13.A6S13821ze
public import CFSG.Quasithin.H13.A6S13822b
public import CFSG.Quasithin.H13.A6S13824h

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.E1.LiftS5 CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement

namespace A6L24

variable {W : Type*} [CommGroup W]

theorem const_of_prod (w : Fin 5 → W) (h : ∀ p, ∏ r ∈ Finset.univ.erase p, w r = 1)
    (p q : Fin 5) : w p = w q := by
  have key : ∀ p, w p = ∏ r, w r := fun p => by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ p), h p, one_mul]
  rw [key p, key q]

theorem prod_erase_eq_one (w : Fin 5 → W) {p : Fin 5} {a b : Perm (Fin 5)}
    (ha : IsV4 p a ∧ a ≠ 1) (hb : IsV4 p b ∧ b ≠ 1 ∧ a ≠ b) {q : Fin 5} (hq : q ≠ p)
    (h : w q * w (a q) * w (b q) * w (b (a q)) = 1) : ∏ r ∈ Finset.univ.erase p, w r = 1 := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hset⟩ := orbit p a ha b hb q hq
  rw [hset, Finset.prod_insert (by simp [h1, h2, h3]), Finset.prod_insert (by simp [h4, h5]),
    Finset.prod_insert (by simp [h6]), Finset.prod_singleton, ← h]
  simp only [mul_assoc]

end A6L24

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_transv_or_quad_VH
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) :
    (∃ x ∈ pCoreOf 2 (S.L1 ⊔ T), InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) ∨
      ∃ Y : Subgroup G, Y ≤ pCoreOf 2 (S.L1 ⊔ T) ∧ ⁅⁅conjClosure V H, Y⁆, Y⁆ = ⊥ ∧
        4 ≤ (Y ⊓ pCoreOf 2 H).relIndex Y := by
  have hF := hS.hF H hH
  by_cases hA : ∃ x ∈ pCoreOf 2 (S.L1 ⊔ T),
      InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)
  · exact Or.inl hA
  right
  push Not at hA
  obtain ⟨γ, γ', g, s, hDγ, hDH, -, hle⟩ := S.case2_of_no_transv_loc hF hA
  have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hS H hH K hK hKn hHK γ γ' g s
    (conjClosure S.V3 H) le_rfl hDH.not_ge
  have hm := S.lem13818Four_loc hS.hNS h13315 h1356two hH hF h13314 hA s hDγ hDH hle hgen
  obtain ⟨c, hcH, hcR⟩ := exists_conj_Vγ_le hF s
  refine ⟨conjSub c (F8.Uγ V H (g : G)), hcR, ?_, ?_⟩
  · have h1 := congrArg (conjSub c) (S.comm_comm_VH_Vγ hF s)
    rwa [← conjSub_commutator, ← conjSub_commutator,
      conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure V H hcH), conjSub_bot] at h1
  · have hY2 : IsPGroup 2 (conjSub c (F8.Uγ V H (g : G))) :=
      (pCoreOf_isPGroup 2 _).to_le hcR
    rw [HypF98.relIndex_eq_two_pow_mIdx hY2]
    have hQ : conjSub c (pCoreOf 2 H) = pCoreOf 2 H :=
      conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hcH)
    rw [← hQ, ← conjSub_inf, F9.mIdx_conjSub]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) :=
        Nat.pow_le_pow_right (by norm_num) hm

theorem mem_M_of_fix_l24
    (h13 : Lem13813) (h1334 : Stmt13_3_4) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHT : H = K ⊔ T) {n : ℕ} (hn : 2 ≤ n) (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {p₀ : Fin 5}
    (hiff : ∀ g : ↥H, quotPerm hKn e g p₀ = p₀ ↔
      (g : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (g : ↥H) (hg : quotPerm hKn e g p₀ = p₀) : (g : G) ∈ Subgroup.normalizer (L : Set G) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hgN := (hiff g).mp hg
  have hB := S.borel_le_M h13 h1334 hS hH hKH hKn hn hLie
  have hg' : (g : G) ∈ ((K ⊔ T : Subgroup G) : Set G) := by
    rw [← hHT]
    exact g.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K T (hTH.trans hKn)] at hg'
  obtain ⟨k, hk, t, ht, hkt⟩ := Set.mem_mul.mp hg'
  have htN : t ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ht) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩
  have hkN : k ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    have e' : k = (g : G) * t⁻¹ := by rw [← hkt]; group
    rw [e']
    exact Subgroup.mul_mem _ hgN (Subgroup.inv_mem _ htN)
  rw [← hkt]
  exact Subgroup.mul_mem _ (hB ⟨hk, hkN⟩) (S.T_le_NL ht)

theorem false_of_quad_l24
    (h13 : Lem13813) (h1334 : Stmt13_3_4) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) {n : ℕ} (hn : 2 ≤ n) (hLie : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (hhat : ¬ IsHatA6 L)
    (hL1K : S.L1 ≤ K) {Y : Subgroup G} (hYR : Y ≤ pCoreOf 2 (S.L1 ⊔ T))
    (hYq : ⁅⁅conjClosure V H, Y⁆, Y⁆ = ⊥) (hY4 : 4 ≤ (Y ⊓ pCoreOf 2 H).relIndex Y) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hLTH : S.L1 ⊔ T ≤ H := hH.1.1
  have hHT : H = K ⊔ T := by rw [hHK, ← sup_assoc, sup_eq_left.mpr hL1K]
  have hYH : Y ≤ H := hYR.trans ((pCoreOf_le 2 _).trans hLTH)
  obtain ⟨p₀, -, -, hiff, hfix⟩ := S.exists_p0_l24 h1334 hS hH hK hKn hn hLie e
  set P := (Y.subgroupOf H).map (quotPerm hKn e) with hP
  have hPV : ∀ σ ∈ P, A6L24.IsV4 p₀ σ := by
    rintro _ ⟨y, hy, rfl⟩
    exact S.isV4_of_mem_R1_l24 hhat hLTH hL1K hKn e hfix (hYR (Subgroup.mem_subgroupOf.mp hy))
  have hP4 : 4 ≤ Nat.card P := by
    rw [hP, ← Subgroup.relIndex_ker]
    have hk : (quotPerm hKn e).ker ≤ (pCoreOf 2 H).subgroupOf H := fun g hg =>
      Subgroup.mem_subgroupOf.mpr (S.mem_QH_of_quotPerm_eq_one hH hKn hHT e g hg)
    calc 4 ≤ (Y ⊓ pCoreOf 2 H).relIndex Y := hY4
      _ = (pCoreOf 2 H).relIndex Y := by rw [Subgroup.inf_relIndex_left]
      _ = ((pCoreOf 2 H).subgroupOf H).relIndex (Y.subgroupOf H) :=
        (Subgroup.relIndex_subgroupOf hYH).symm
      _ ≤ (quotPerm hKn e).ker.relIndex (Y.subgroupOf H) :=
        Subgroup.relIndex_le_of_le_left hk (relIndex_ne_zero' _ _)
  have hall : ∀ τ, A6L24.IsV4 p₀ τ → τ ∈ P := by
    have ht : {σ : Perm (Fin 5) | A6L24.IsV4 p₀ σ} =
        ↑(Finset.univ.filter (A6L24.IsV4 p₀)) := by
      ext σ
      simp
    have hsub : (P : Set (Perm (Fin 5))) ⊆ {σ | A6L24.IsV4 p₀ σ} := fun σ hσ => hPV σ hσ
    have hle : {σ : Perm (Fin 5) | A6L24.IsV4 p₀ σ}.ncard ≤ (P : Set (Perm (Fin 5))).ncard := by
      rw [ht, Set.ncard_coe_finset, A6L24.card_isV4, ← Nat.card_coe_set_eq]
      exact hP4
    have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
    intro τ hτ
    have h1 : τ ∈ (P : Set (Perm (Fin 5))) := by
      rw [heq]
      exact hτ
    exact h1
  obtain ⟨α, β, hα, hβ, hα1, hβ1, hαβ⟩ := A6L24.v4_gen p₀
  obtain ⟨a₀, ha₀Y, ha₀⟩ := hall α hα
  obtain ⟨b₀, hb₀Y, hb₀⟩ := hall β hβ
  have hquad : ∀ v ∈ conjClosure V H, ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, ⁅⁅v, y₁⁆, y₂⁆ = 1 := by
    intro v hv y₁ hy₁ y₂ hy₂
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hv hy₁) hy₂
    rw [hYq] at h1
    exact h1
  have hVab : IsElemAbelian 2 (conjClosure V H) :=
    HypF91.isElemAbelian_conjClosure_of_forall S.elemAbelian_V fun k hk v hv => by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 : v ∈ conjClosure V S.G1 := le_conjClosure V S.G1 hv
      have h2 : w ∈ conjClosure V S.G1 := HypF91.conjSub_le_conjClosure (hH.2.1 hk) hw
      exact congrArg Subtype.val (hS.hab.is_comm.comm ⟨w, h2⟩ ⟨v, h1⟩)
  set VH := conjClosure V H with hVHdef
  set UH := conjClosure S.V3 H with hUHdef
  have hF := (hS.hF H hH).toHypF91
  have hUN : H ≤ Subgroup.normalizer (UH : Set G) := le_normalizer_conjClosure S.V3 H
  have hVN : H ≤ Subgroup.normalizer (VH : Set G) := le_normalizer_conjClosure V H
  have hUV : UH ≤ VH := conjClosure_mono S.V3_le_V le_rfl
  have hconj : ∀ (g : ↥H) (x : G), x ∈ VH → (g : G) * x * (g : G)⁻¹ ∈ VH := fun g x hx =>
    (Subgroup.mem_normalizer_iff.mp (hVN g.2) x).mp hx
  obtain ⟨v₀, hv₀V, hv₀U⟩ :=
    SetLike.not_le_iff_exists.mp (S.V_not_le_UH hS.hNS h13315 h1356two hH h13314)
  have hv₀VH : v₀ ∈ VH := le_conjClosure V H hv₀V
  have hidx : (S.V3.subgroupOf V).index = 2 := S.relIndex_V3_V
  have hV3U : S.V3 ≤ UH := le_conjClosure _ _
  have hmodV : ∀ u ∈ V, ∀ v ∈ V, u ∉ UH → v ∉ UH → u * v⁻¹ ∈ UH := by
    intro u hu v hv huU hvU
    have hu3 : (⟨u, hu⟩ : ↥V) ∉ S.V3.subgroupOf V := fun h =>
      huU (hV3U (Subgroup.mem_subgroupOf.mp h))
    have hv3 : (⟨v, hv⟩ : ↥V)⁻¹ ∉ S.V3.subgroupOf V := fun h => hvU (by
      have h1 := UH.inv_mem (hV3U (Subgroup.mem_subgroupOf.mp h))
      simpa using h1)
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hu3 hv3)
    exact hV3U (Subgroup.mem_subgroupOf.mp h1)
  have : IsMulCommutative ↥VH := hVab.1
  set N : Subgroup ↥VH := UH.subgroupOf VH with hN
  let mkW : ∀ x : G, x ∈ VH → ↥VH ⧸ N := fun x hx => QuotientGroup.mk ⟨x, hx⟩
  have mkW_congr : ∀ (x y : G) (hx : x ∈ VH) (hy : y ∈ VH), x = y → mkW x hx = mkW y hy := by
    intro x y hx hy h
    subst h
    rfl
  have mkW_eq : ∀ (x y : G) (hx : x ∈ VH) (hy : y ∈ VH), mkW x hx = mkW y hy ↔ x⁻¹ * y ∈ UH := by
    intro x y hx hy
    show (QuotientGroup.mk _ : ↥VH ⧸ N) = QuotientGroup.mk _ ↔ _
    rw [QuotientGroup.eq, hN, Subgroup.mem_subgroupOf]
    rfl
  have mkW_mul : ∀ (x y : G) (hx : x ∈ VH) (hy : y ∈ VH),
      mkW (x * y) (VH.mul_mem hx hy) = mkW x hx * mkW y hy := fun _ _ _ _ => rfl
  have mkW_inv : ∀ (x : G) (hx : x ∈ VH), mkW x⁻¹ (VH.inv_mem hx) = (mkW x hx)⁻¹ :=
    fun _ _ => rfl
  have hW2 : ∀ q : ↥VH ⧸ N, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul]
      have h1 : x * x = 1 := Subtype.ext (by
        have := hVab.2 x x.2
        rw [sq] at this
        simpa using this)
      rw [h1, QuotientGroup.mk_one]
  have hinv : ∀ q : ↥VH ⧸ N, q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_right (hW2 q)
  have hk : ∀ q : Fin 5, ∃ k : ↥H, quotPerm hKn e k p₀ = q := fun q => by
    obtain ⟨σ, hσs, hσ⟩ := A6L24.exists_even_map p₀ q
    obtain ⟨k, -, hk⟩ := A6L24.exists_lift hKH hKn e (Perm.mem_alternatingGroup.mpr hσs)
    exact ⟨k, by rw [hk, hσ]⟩
  choose kq hkq using hk
  let w : Fin 5 → ↥VH ⧸ N := fun q =>
    mkW ((kq q : G) * v₀ * (kq q : G)⁻¹) (hconj (kq q) v₀ hv₀VH)
  have hwd : ∀ (g : ↥H) (q : Fin 5), quotPerm hKn e g p₀ = q →
      mkW ((g : G) * v₀ * (g : G)⁻¹) (hconj g v₀ hv₀VH) = w q := by
    intro g q hgq
    set m : ↥H := (kq q)⁻¹ * g with hm
    have hmp : quotPerm hKn e m p₀ = p₀ := by
      rw [hm, map_mul, map_inv, Perm.mul_apply, hgq, Perm.inv_eq_iff_eq, hkq]
    have hmM := S.mem_M_of_fix_l24 h13 h1334 hS hH hK hKn hHT hn hLie e hiff m hmp
    have hmV : (m : G) ∈ Subgroup.normalizer (V : Set G) := S.inf_M_le_NV' hH ⟨m.2, hmM⟩
    set u := (m : G) * v₀ * (m : G)⁻¹ with hu
    have huV : u ∈ V := (Subgroup.mem_normalizer_iff.mp hmV v₀).mp hv₀V
    have huU : u ∉ UH := by
      intro h
      apply hv₀U
      have h1 := (Subgroup.mem_normalizer_iff.mp (hUN (H.inv_mem m.2)) u).mp h
      have e' : (m : G)⁻¹ * u * ((m : G)⁻¹)⁻¹ = v₀ := by rw [hu]; group
      rw [e'] at h1
      exact h1
    have h1 : u⁻¹ * v₀ ∈ UH := by
      have h2 := hmodV u⁻¹ (V.inv_mem huV) v₀⁻¹ (V.inv_mem hv₀V)
        (fun h => huU (by simpa using UH.inv_mem h)) (fun h => hv₀U (by simpa using UH.inv_mem h))
      simpa using h2
    show mkW _ _ = mkW _ _
    rw [mkW_eq]
    have e' : ((g : G) * v₀ * (g : G)⁻¹)⁻¹ * ((kq q : G) * v₀ * (kq q : G)⁻¹) =
        (kq q : G) * (u⁻¹ * v₀) * (kq q : G)⁻¹ := by
      have hg : (g : G) = (kq q : G) * m := by rw [hm]; push_cast; group
      rw [hg, hu]
      group
    rw [e']
    exact (Subgroup.mem_normalizer_iff.mp (hUN (kq q).2) _).mp h1
  have hact : ∀ (g : ↥H) (q : Fin 5) (hx : (g : G) * ((kq q : G) * v₀ * (kq q : G)⁻¹) *
      (g : G)⁻¹ ∈ VH), mkW _ hx = w (quotPerm hKn e g q) := by
    intro g q hx
    rw [← hwd (g * kq q) (quotPerm hKn e g q) (by rw [map_mul, Perm.mul_apply, hkq])]
    exact mkW_congr _ _ _ _ (by push_cast; group)
  have h4term : ∀ (a b : ↥H), (∀ v ∈ VH, ⁅⁅v, (a : G)⁆, (b : G)⁆ = 1) → ∀ q : Fin 5,
      w q * w (quotPerm hKn e a q) * w (quotPerm hKn e b q) *
        w (quotPerm hKn e b (quotPerm hKn e a q)) = 1 := by
    intro a b hab q
    set v := (kq q : G) * v₀ * (kq q : G)⁻¹ with hv
    have hvVH : v ∈ VH := hconj (kq q) v₀ hv₀VH
    set α' := (a : G) * v * (a : G)⁻¹ with hα'
    have hαVH : α' ∈ VH := hconj a v hvVH
    have hcomm : (b : G) * (v * α'⁻¹) * (b : G)⁻¹ = v * α'⁻¹ := by
      have hc := hab v hvVH
      have h1 : ⁅v, (a : G)⁆ = v * α'⁻¹ := by rw [commutatorElement_def, hα']; group
      rw [h1] at hc
      rw [← (commutatorElement_eq_one_iff_commute.mp hc).eq, mul_inv_cancel_right]
    have hX : mkW ((b : G) * v * (b : G)⁻¹) (hconj b v hvVH) = w (quotPerm hKn e b q) :=
      hact b q _
    have hU : mkW α' hαVH = w (quotPerm hKn e a q) := hact a q _
    have hY : mkW ((b : G) * α' * (b : G)⁻¹) (hconj b α' hαVH) =
        w (quotPerm hKn e b (quotPerm hKn e a q)) := by
      have h1 := hact (b * a) q (hconj (b * a) v hvVH)
      rw [map_mul, Perm.mul_apply] at h1
      rw [← h1]
      exact mkW_congr _ _ _ _ (by rw [hα', hv]; push_cast; group)
    have hrel : mkW ((b : G) * v * (b : G)⁻¹) (hconj b v hvVH) *
        (mkW ((b : G) * α' * (b : G)⁻¹) (hconj b α' hαVH))⁻¹ = mkW v hvVH * (mkW α' hαVH)⁻¹ := by
      rw [← mkW_inv, ← mkW_inv, ← mkW_mul, ← mkW_mul]
      exact mkW_congr _ _ _ _ (by rw [← hcomm]; group)
    rw [hX, hY, hU, hinv, hinv] at hrel
    have hwq : mkW v hvVH = w q := rfl
    rw [hwq] at hrel
    rw [mul_assoc (w q * w (quotPerm hKn e a q)), ← hrel]
    exact hW2 _
  have hprod : ∀ p : Fin 5, ∏ r ∈ Finset.univ.erase p, w r = 1 := by
    intro p
    set h := kq p with hh
    set ψh := quotPerm hKn e h
    have hp : ψh p₀ = p := hkq p
    have hψa : quotPerm hKn e (h * a₀ * h⁻¹) = ψh * α * ψh⁻¹ := by
      rw [map_mul, map_mul, map_inv, ha₀]
    have hψb : quotPerm hKn e (h * b₀ * h⁻¹) = ψh * β * ψh⁻¹ := by
      rw [map_mul, map_mul, map_inv, hb₀]
    have hconj1 : ∀ x : Perm (Fin 5), ψh * x * ψh⁻¹ = 1 → x = 1 := fun x hx => by
      have h1 := congrArg (fun y => ψh⁻¹ * y * ψh) hx
      simpa [mul_assoc] using h1
    have hav : A6L24.IsV4 p (quotPerm hKn e (h * a₀ * h⁻¹)) := by
      rw [hψa, ← hp]
      exact A6L24.isV4_conj hα ψh
    have hbv : A6L24.IsV4 p (quotPerm hKn e (h * b₀ * h⁻¹)) := by
      rw [hψb, ← hp]
      exact A6L24.isV4_conj hβ ψh
    have ha1 : quotPerm hKn e (h * a₀ * h⁻¹) ≠ 1 := by
      rw [hψa]
      exact fun h1 => hα1 (hconj1 α h1)
    have hb1 : quotPerm hKn e (h * b₀ * h⁻¹) ≠ 1 := by
      rw [hψb]
      exact fun h1 => hβ1 (hconj1 β h1)
    have hab : quotPerm hKn e (h * a₀ * h⁻¹) ≠ quotPerm hKn e (h * b₀ * h⁻¹) := by
      rw [hψa, hψb]
      intro h1
      apply hαβ
      have h2 := congrArg (fun y => ψh⁻¹ * y * ψh) h1
      simpa [mul_assoc] using h2
    have hq : ∀ v ∈ VH, ⁅⁅v, ((h * a₀ * h⁻¹ : ↥H) : G)⁆, ((h * b₀ * h⁻¹ : ↥H) : G)⁆ = 1 := by
      intro v hv
      have hv' : (h : G)⁻¹ * v * (h : G) ∈ VH := by simpa using hconj h⁻¹ v hv
      have h1 := hquad _ hv' a₀ (Subgroup.mem_subgroupOf.mp ha₀Y) b₀
        (Subgroup.mem_subgroupOf.mp hb₀Y)
      have e' : ⁅⁅v, ((h * a₀ * h⁻¹ : ↥H) : G)⁆, ((h * b₀ * h⁻¹ : ↥H) : G)⁆ =
          (h : G) * ⁅⁅(h : G)⁻¹ * v * (h : G), (a₀ : G)⁆, (b₀ : G)⁆ * (h : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e', h1, mul_one, mul_inv_cancel]
    have hqp : p + 1 ≠ p := by
      have key : ∀ p : Fin 5, p + 1 ≠ p := by decide
      exact key p
    exact A6L24.prod_erase_eq_one w ⟨hav, ha1⟩ ⟨hbv, hb1, hab⟩ hqp (h4term _ _ hq (p + 1))
  have hconst := A6L24.const_of_prod w hprod
  have hw₀ : ∀ g : ↥H, ((g : G) * v₀ * (g : G)⁻¹)⁻¹ * v₀ ∈ UH := by
    intro g
    have h1 := hwd g _ rfl
    have h2 := hwd 1 p₀ (by rw [map_one, Perm.one_apply])
    rw [hconst (quotPerm hKn e g p₀) p₀, ← h2] at h1
    have h3 := (mkW_eq _ _ _ _).mp h1
    simpa using h3
  have hfinal : conjClosure V H ≤ V ⊔ UH := by
    refine conjClosure_le fun g hg v hv => ?_
    by_cases hvU : v ∈ UH
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hUN hg) v).mp hvU)
    · have h1 : v * v₀⁻¹ ∈ UH := hmodV v hv v₀ hv₀V hvU hv₀U
      have h2 := hw₀ ⟨g, hg⟩
      have e' : g * v * g⁻¹ = (g * (v * v₀⁻¹) * g⁻¹) * (v₀ * ((g * v₀ * g⁻¹)⁻¹ * v₀)⁻¹) := by
        group
      rw [e']
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hUN hg) _).mp h1))
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left hv₀V) (Subgroup.mem_sup_right (UH.inv_mem h2)))
  exact S.VH_not_le_V_sup_UH hS.hNS h13315 h1356two hH h13314 hfinal

end Setting4

end CFSG.Quasithin.H13.A6
