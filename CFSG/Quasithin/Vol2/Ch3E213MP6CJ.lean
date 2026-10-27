module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CI
public import CFSG.Quasithin.Vol2.Ch3E213MLift
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
public import CFSG.Quasithin.Vol2.Ch3E213MKer

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiUnipotent)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G]

theorem inf_pCoreOf_le' [Finite G] {H X V : Subgroup G} (hXH : X ≤ H) (hVX : V ≤ X) :
    V ⊓ pCoreOf 2 H ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_trans (le_inf inf_le_right (inf_le_left.trans hVX))
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left))
  exact (le_inf (hXH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem kerIn_map_eq_bot {G' : Type} [Group G'] {f : G' →* G} (hf : Function.Injective f)
    {P Y : Subgroup G'} (h : kerIn P Y = ⊥) : kerIn (P.map f) (Y.map f) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ : z ∈ P.map f := by simpa using hz 1 (Subgroup.one_mem _)
  have hk : z₀ ∈ kerIn P Y := fun y hy => by
    obtain ⟨p, hp, hpe⟩ := hz (f y) ⟨y, hy, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at hpe
    rwa [← hf hpe]
  rw [h, Subgroup.mem_bot] at hk
  rw [hk, map_one]
  exact Subgroup.one_mem _

theorem exists_orderOf_eq_of_surj {X L : Type*} [Group X] [Finite X] [Group L] {φ : X →* L}
    (hφ : Function.Surjective φ) {c : L} {n : ℕ} (hc : orderOf c = n) :
    ∃ x : X, orderOf x = n := by
  obtain ⟨y, rfl⟩ := hφ c
  have hdvd : n ∣ orderOf y := hc ▸ orderOf_map_dvd φ y
  exact ⟨y ^ (orderOf y / n), orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd⟩

theorem exists_hom_of_map_subtype {H : Subgroup G} {I : Subgroup H} {X : Subgroup G}
    (hIX : I.map H.subtype = X) {L : Type*} [Group L] (φ : ↥I →* L)
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.pCore 2 ↥I) :
    ∃ φ' : ↥X →* L, Function.Surjective φ' ∧ φ'.ker = (pCoreOf 2 X).subgroupOf X := by
  subst hIX
  set e : ↥I ≃* ↥(I.map H.subtype) := I.equivMapOfInjective _ H.subtype_injective
  refine ⟨φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, ?_⟩
  have h1 : (pCoreOf 2 (I.map H.subtype)).subgroupOf (I.map H.subtype) =
      CFSG.pCore 2 ↥(I.map H.subtype) := by
    rw [pCoreOf, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
  rw [h1, ← CFSG.pCore_map_iso 2 e]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
  constructor
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

variable [Finite G]

theorem exists_coord_member {H T M V K : Subgroup G} (hS : Setting H T M V K)
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)))
    {k : Type} [Field k] [Finite k] [CharP k 2] (D : Sp4Data H T M V K k)
    {Y : Subgroup (antiSp k)} {g : antiSp k} (hgY : g ∈ Y)
    (hY : coordIn D.θ V ⊔ (coordIn D.θ V).map (MulAut.conj g).toMonoidHom = Y)
    (hSyl : IsSylowOf 2 (Y ⊓ antiUnipotent k) Y)
    (hcore : kerIn (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) Y = ⊥)
    (hO2 : CFSG.inSubgroup (CFSG.pCore 2) Y = ⊥)
    (hO2B : CFSG.inSubgroup (CFSG.pCore 2)
      (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) = Y ⊓ antiUnipotent k)
    (hexact : OddCoverExact ↥Y) :
    ∃ g ∈ H, E2.Pair (Ch3n.pairI V g) (T ⊓ Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g ∧
      CharTwo (Ch3n.pairI V g) ∧ Ch3n.pairI V g ≠ V ∧
      kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) = pCoreOf 2 (Ch3n.pairI V g) ∧
      (∃ φ : ↥(Ch3n.pairI V g) →* ↥Y, Function.Surjective φ ∧
        φ.ker = (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g)).subgroupOf (Ch3n.pairI V g)) ∧
      (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V).relIndex V ≤
        Nat.card (coordIn D.θ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := hS.hyp.minParabolic
  have hTH : T ≤ H := hmp.isSylow.1
  have hMH : M ≤ H := hmp.maximal.1.le
  have hVH : V ≤ H := hS.hyp.le_H
  have hTM : T ≤ M := hmp.le
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  have hVQ : ¬ V.subgroupOf H ≤ CFSG.pCore 2 H := fun h => by
    rw [inf_eq_left.2 h, Subgroup.relIndex_self] at hVQ'
    omega
  set ψ := coordMap D with hψdef
  have hψinj : Function.Injective ψ := coordMap_injective D
  set W := coordIn D.θ V with hWdef
  set F := Y.map ψ with hFdef
  set SF := (Y ⊓ antiUnipotent k).map ψ with hSFdef
  set PF := (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))).map ψ with hPFdef
  have hbot : IsElementaryAbelian 2 (⊥ : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤)) :=
    { is_comm := ⟨fun _ _ => Subsingleton.elim _ _⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun _ => Subsingleton.elim _ _ }
  have hVbar : (V.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) = W.map ψ :=
    (map_coordMap_coordIn D D.V_le).symm
  have hFA : ∀ f ∈ F, ∀ a ∈ (⊥ : Subgroup (↥H ⧸ kerIn (M.subgroupOf H) ⊤)), f * a = a * f :=
    fun f _ a ha => by rw [Subgroup.mem_bot.1 ha, mul_one, one_mul]
  have hxL : (ψ g)⁻¹ ∈ F ⊔ ⊥ := by
    rw [sup_bot_eq]
    exact F.inv_mem ⟨g, hgY, rfl⟩
  have hL : F ⊔ ⊥ = (V.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) ⊔
      CFSG.conjugate ((V.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)))
        (ψ g)⁻¹ := by
    rw [sup_bot_eq, hVbar, hFdef, ← hY, Subgroup.map_sup, CFSG.conjugate, inv_inv,
      Subgroup.map_map, Subgroup.map_map]
    congr 2
    ext w
    simp [MulAut.conj_apply]
  have hFnt : F ≠ ⊥ := by
    intro h
    have hW : W ≤ ⊥ := by
      intro w hw
      have h1 : ψ w ∈ F := ⟨w, hY ▸ (le_sup_left : W ≤ _) hw, rfl⟩
      rw [h, Subgroup.mem_bot, ← map_one ψ] at h1
      rw [hψinj h1]
      exact Subgroup.one_mem _
    exact D.V_not_le_long (hW.trans bot_le)
  have hexact' : OddCoverExact ↥F :=
    OddCoverExact.of_mulEquiv (Y.equivMapOfInjective ψ hψinj).symm hexact
  have hSF : IsSylowOf 2 SF F :=
    CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective ψ hψinj hSyl
  have hPF : PF ≤ F := Subgroup.map_mono inf_le_left
  have hPFcore : kerIn PF F = ⊥ := kerIn_map_eq_bot hψinj hcore
  have hFO : CFSG.inSubgroup (CFSG.pCore 2) F = ⊥ := by
    rw [hFdef, ← CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore_of_injective 2 ψ
      hψinj, hO2, Subgroup.map_bot]
  have hPFO : CFSG.inSubgroup (CFSG.pCore 2) PF = SF := by
    rw [hPFdef, ← CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore_of_injective 2 ψ
      hψinj, hO2B]
  have hSL : (T' : Subgroup H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) ⊓ (F ⊔ ⊥) =
      SF ⊔ ⊥ := by
    rw [sup_bot_eq, sup_bot_eq, hT']
    change barIn M H T ⊓ Y.map ψ = SF
    rw [barIn_inf_map_coordMap, D.sylow, inf_comm]
  have hBL : (M.subgroupOf H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤)) ⊓ (F ⊔ ⊥) =
      PF ⊔ ⊥ := by
    rw [sup_bot_eq, sup_bot_eq]
    change barIn M H M ⊓ Y.map ψ = PF
    rw [barIn_inf_map_coordMap, coordIn_M_eq hMH hB D hTM, inf_comm]
  obtain ⟨g₀, hgI, hVI, -, -, -, -, -, -, -, -, hTIsyl, -, -, hJ1, hJ2, -, -, hcharI, hO2MI, hNV,
      ψI, hψs, hψker, -, -, -, -⟩ :=
    pair_lift_of_oddCoverExact hcharH T' hTn hTM' hMH' hmax' hVT' hTV' hVM' hVQ
      (F := F) (A := ⊥) hFA (inf_bot_eq _) hxL hL hFnt hexact' hSF hPF hPFcore hFO hPFO hSL hBL
  rw [hT'] at hTIsyl hO2MI
  have hVMI : V.subgroupOf H ≤ CFSG.inSubgroup (CFSG.pCore 2)
      (M.subgroupOf H ⊓ (V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g₀)) := by
    rw [hO2MI]
    exact le_inf (hT' ▸ hVT') le_sup_left
  obtain ⟨hIX, hpair, hker⟩ := pair_of_qrc_kerIn hTH hMH hS.hyp.le_T hS.hyp.normal_T
    hS.hyp.elem rfl hgI hTIsyl (fun x hx => (hNV ⟨hx.2, hx.1⟩).1) hVMI (hJ1.symm.trans hJ2)
  obtain ⟨hc2, hne⟩ := charTwo_ne_of_qrc hVH hcharI hVI
  rw [hIX] at hc2 hne
  have hXH : Ch3n.pairI V (g₀ : G)⁻¹ ≤ H := by
    rw [← hIX]
    exact Subgroup.map_subtype_le _
  have hle : V ⊓ pCoreOf 2 H ≤
      kerIn (M ⊓ Ch3n.pairI V (g₀ : G)⁻¹) (Ch3n.pairI V (g₀ : G)⁻¹) ⊓ V := by
    rw [hker]
    exact le_inf (inf_pCoreOf_le' hXH hpair.V_le) inf_le_left
  have hWcard : Nat.card W = (V ⊓ pCoreOf 2 H).relIndex V := by
    rw [← D.card_V, ← map_coordMap_coordIn D D.V_le, Subgroup.card_map_of_injective hψinj]
  have hpos : 0 < (V ⊓ pCoreOf 2 H).relIndex V := by
    rw [← hWcard]
    exact Nat.card_pos
  have hVB : (kerIn (M ⊓ Ch3n.pairI V (g₀ : G)⁻¹) (Ch3n.pairI V (g₀ : G)⁻¹) ⊓ V).relIndex V ≤
      Nat.card W := by
    rw [hWcard]
    exact Nat.le_of_dvd hpos (Subgroup.relIndex_dvd_of_le_left V hle)
  have hψk' : ψI.ker = CFSG.pCore 2 ↥(V.subgroupOf H ⊔ CFSG.conjugate (V.subgroupOf H) g₀) := by
    rw [hψker, hJ2, CFSG.inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_of_map_subtype hIX ψI hψs hψk'
  refine ⟨(g₀ : G)⁻¹, H.inv_mem g₀.2, hpair, hc2, hne, hker,
    ⟨(Y.equivMapOfInjective ψ hψinj).symm.toMonoidHom.comp φ,
      (Y.equivMapOfInjective ψ hψinj).symm.surjective.comp hφs, ?_⟩, hVB⟩
  have hk : ((Y.equivMapOfInjective ψ hψinj).symm.toMonoidHom.comp φ).ker = φ.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  rw [hk, hφk, hker]

theorem e213Concl_of_coord_member {H T M V K : Subgroup G} (hS : Setting H T M V K)
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)))
    {k : Type} [Field k] [Finite k] [CharP k 2] (D : Sp4Data H T M V K k)
    {Y : Subgroup (antiSp k)} {g : antiSp k} (hgY : g ∈ Y)
    (hY : coordIn D.θ V ⊔ (coordIn D.θ V).map (MulAut.conj g).toMonoidHom = Y)
    (hSyl : IsSylowOf 2 (Y ⊓ antiUnipotent k) Y)
    (hcore : kerIn (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) Y = ⊥)
    (hO2 : CFSG.inSubgroup (CFSG.pCore 2) Y = ⊥)
    (hO2B : CFSG.inSubgroup (CFSG.pCore 2)
      (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) = Y ⊓ antiUnipotent k)
    (hexact : OddCoverExact ↥Y)
    (hstar : ∃ c ∈ Y, ∃ ℓ a : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf c = ℓ ^ (a + 1) ∧
      ∀ m : ℕ, 0 < m → ℓ ^ (a + 1) ∣ 2 ^ m - 1 → Nat.card (coordIn D.θ V) ^ 2 ≤ 2 ^ m) :
    E213Concl H T M V := by
  obtain ⟨g', hg', hpair, hc2, hne, -, ⟨φ, hφs, -⟩, hVB⟩ :=
    exists_coord_member hS hB D hgY hY hSyl hcore hO2 hO2B hexact
  obtain ⟨c, hcY, ℓ, a, hℓ, hℓ2, hc, hm⟩ := hstar
  obtain ⟨x, hxo⟩ := exists_orderOf_eq_of_surj hφs (c := (⟨c, hcY⟩ : ↥Y))
    (n := ℓ ^ (a + 1)) (by rw [← Subgroup.orderOf_coe]; exact hc)
  refine ⟨g', hg', hpair, hc2, hne, relIndex_le_of_orderOf hpair hc2 x.2 hℓ hℓ2
    (by rw [Subgroup.orderOf_coe]; exact hxo) fun m hm0 hdvd => ?_⟩
  exact (Nat.pow_le_pow_left hVB 2).trans (hm m hm0 hdvd)

end CFSG.Quasithin.Ch3E213M
