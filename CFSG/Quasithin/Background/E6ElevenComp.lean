module

public import CFSG.Quasithin.Background.E6ElevenTwo
public import CFSG.Quasithin.Background.E6EightFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique
open scoped Function

section General

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_inf_of_subnormal' {K L Q : Subgroup G} (hQ : IsSylowTwoOf Q K)
    (hLK : L ≤ K) (hsub : (L.subgroupOf K).IsSubnormal) : IsSylowTwoOf (Q ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (Q.subgroupOf K) :=
    hQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm
  set S : Sylow 2 K := hQ2.toSylow hQ.2.2 with hSdef
  have hS : (S : Subgroup K).map K.subtype = Q := by
    change (Q.subgroupOf K).map K.subtype = Q
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ.1]
  obtain ⟨P', hP'⟩ := exists_sylow_map_eq_inf_of_subnormal S hsub
  let e : (L.subgroupOf K) ≃* L := Subgroup.subgroupOfEquivOfLe hLK
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  set P : Sylow 2 L := P'.mapSurjective he with hPdef
  have hPmap : (P : Subgroup L).map L.subtype = Q ⊓ L := by
    rw [hPdef, Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : L.subtype.comp e.toMonoidHom = K.subtype.comp (L.subgroupOf K).subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hP', Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hS,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLK]
  rw [← hPmap]
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map L.subtype, ?_⟩
  change ¬ 2 ∣ (((P : Subgroup L).map L.subtype).comap L.subtype).index
  rw [Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  exact P.not_dvd_index

omit [Finite G] in
theorem mem_conjugate_iff' (Z : Subgroup G) (c y : G) :
    y ∈ CFSG.conjugate Z c ↔ c * y * c⁻¹ ∈ Z := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hh
    refine ⟨c * y * c⁻¹, hh, ?_⟩
    simp [mul_assoc]

omit [Finite G] in
theorem pPrimeCore_eq_bot_of_oddCoreIn' {H : Subgroup G} (hO : oddCoreIn H = ⊥) :
    CFSG.pPrimeCore 2 ↥H = ⊥ := by
  have h1 : fusionOddCore ↥H = ⊥ := by
    unfold oddCoreIn at hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hO
  rw [← h1]
  unfold CFSG.pPrimeCore fusionOddCore
  congr 1
  ext K
  show (K.Normal ∧ Nat.Coprime 2 (Nat.card K)) ↔ (K.Normal ∧ Odd (Nat.card K))
  rw [Nat.coprime_two_left]

theorem mem_twoPrimeResidual_of_pow' {H : Subgroup G} {x : G} (hx : x ∈ H) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ twoPrimeResidual H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hle : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hx
  refine Subgroup.mem_iInf.mpr fun N => Subgroup.mem_iInf.mpr fun hN => ?_
  exact B6.le_of_isPGroup_of_odd_relIndex hle hP hN.1 hN.2.1 hN.2.2 (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer {L : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hc : c ∈ Subgroup.centralizer (L : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).1 hl
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hl'
  calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * l := by group

omit [Finite G] in
theorem mem_centralizer_of_odd {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V) {g : G}
    {o : ℕ} (ho : Odd o) (hgo : g ^ o = 1) (hgU : ∀ u ∈ U, g * u = u * g)
    (hgV : ∀ a ∈ V, g * a * g⁻¹ * a⁻¹ ∈ U) : g ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨u, hudef⟩ : ∃ u, u = g * a * g⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hu : u ∈ U := hudef ▸ hgV a ha
  have hga : g * a * g⁻¹ = u * a := by rw [hudef]; group
  have hk : ∀ k : ℕ, g ^ k * a * (g ^ k)⁻¹ = u ^ k * a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hgu : g * u ^ k * g⁻¹ = u ^ k := by
        rw [hgU _ (U.pow_mem hu k), mul_inv_cancel_right]
      calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (u ^ k * a) * g⁻¹ := by rw [ih]
        _ = (g * u ^ k * g⁻¹) * (g * a * g⁻¹) := by group
        _ = u ^ (k + 1) * a := by rw [hgu, hga, pow_succ]; group
  have h1 := hk o
  rw [hgo, one_mul, inv_one, mul_one] at h1
  have huo : u ^ o = 1 := by
    have := congrArg (· * a⁻¹) h1
    simpa using this.symm
  have hu2 : u ^ 2 = 1 := hV.2 u (hUV hu)
  obtain ⟨m, rfl⟩ := ho
  have hu1 : u = 1 := by
    have : u ^ (2 * m + 1) = (u ^ 2) ^ m * u := by rw [pow_succ, pow_mul]
    rw [this, hu2, one_pow, one_mul] at huo
    exact huo
  have : g * a * g⁻¹ = a := by rw [hga, hu1, one_mul]
  calc a * g = (g * a * g⁻¹) * g := by rw [this]
    _ = g * a := by group

theorem noncommProd_comp_equiv {α β : Type*} [Monoid β] (s : Finset α) (e : α ≃ α)
    (he : ∀ a, a ∈ s ↔ e a ∈ s) (g : α → β) (comm comm') :
    s.noncommProd (g ∘ e) comm' = s.noncommProd g comm := by
  classical
  have hs : s.map e.toEmbedding = s := by
    ext a
    rw [Finset.mem_map_equiv, he (e.symm a), Equiv.apply_symm_apply]
  have hval : s.val.map e = s.val := by
    have := congrArg Finset.val hs
    rwa [Finset.map_val] at this
  have h1 : s.val.map (g ∘ e) = s.val.map g := by
    rw [← Multiset.map_map, hval]
  unfold Finset.noncommProd
  have key : ∀ (m₁ m₂ : Multiset β) (_ : m₁ = m₂) (c₁ c₂),
      Multiset.noncommProd m₁ c₁ = Multiset.noncommProd m₂ c₂ := by
    intro m₁ m₂ hm c₁ c₂
    subst hm
    rfl
  exact key _ _ h1 _ _

theorem noncommProd_pow' {α β : Type*} [Monoid β] (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise (Commute on f)) (n : ℕ)
    (comm' : (s : Set α).Pairwise (Commute on fun a => f a ^ n)) :
    (s.noncommProd f comm) ^ n = s.noncommProd (fun a => f a ^ n) comm' := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.noncommProd_cons, Finset.noncommProd_cons]
    have hc : Commute (f a) (s.noncommProd f (comm.mono fun _ => Finset.mem_cons_of_mem)) :=
      Finset.noncommProd_commute _ _ _ _ fun y hy =>
        comm (Finset.mem_cons_self a s) (Finset.mem_cons_of_mem hy)
          (ne_of_mem_of_not_mem hy ha).symm
    rw [hc.mul_pow, ih (comm.mono fun _ => Finset.mem_cons_of_mem)
      (comm'.mono fun _ => Finset.mem_cons_of_mem)]

end General

theorem e611ComponentCase_of (hE68 : E68ComponentFacts) (hlist : Lemma115_3_List) :
    E611ComponentCase := by
  intro G _ _ T M V U L h hU hmax hn hO hL
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hQ2 : IsPGroup 2 Q := hQH.2.1
  have hVH : V ≤ H := hVQ.trans hQH.1
  have hQH' : Q ≤ H := hQH.1
  have hLH : L ≤ H := hL.1
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hUV : U ≤ V := hU.1
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hLM : ¬ L ≤ M := fun hLM => DoubleA3.not_isComponentIn_of_charTwo (e6_6_one h hUV) L
    (BenderBranch.isComponentIn_of_le hL (le_inf hLM hLH) inf_le_right)
  have hUC : U ≤ V ⊓ Subgroup.centralizer (L : Set G) := le_inf hUV fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun l hl => (Subgroup.mem_centralizer_iff.1 (hLH hl) u hu).symm
  have hCV : V ⊓ Subgroup.centralizer (L : Set G) = U := by
    by_contra hne
    have hlt : U < V ⊓ Subgroup.centralizer (L : Set G) := lt_of_le_of_ne hUC (Ne.symm hne)
    apply hLM
    refine le_trans (fun l hl => ?_) (hmax _ hlt inf_le_left)
    exact Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hw.2 l hl).symm
  have hidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V = 2 ^ E3.mQuot V U := by
    rw [hCV]
    exact E3.relIndex_eq_two_pow hV2 U
  have hSL : IsSylowTwoOf (Q ⊓ L) L := isSylowTwoOf_inf_of_subnormal' hQH hLH hL.2.2
  have hcoreH : CFSG.pPrimeCore 2 ↥H = ⊥ := pPrimeCore_eq_bot_of_oddCoreIn' hO
  have hQ2' : IsPGroup 2 (Q.subgroupOf H) :=
    hQH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQH.1).symm
  set P : Sylow 2 ↥H := hQ2'.toSylow hQH.2.2 with hPdef
  have hVN : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G) := by
    intro v hv
    have hvz : (⟨v, hVH hv⟩ : ↥H) ∈ Subgroup.centralizer ((P : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hQV (show (y : G) ∈ Q from hy)) v hv).symm
    have hvzS : (⟨v, hVH hv⟩ : ↥H) ∈ (P : Subgroup ↥H) := show v ∈ Q from hVQ hv
    have hnorm := central_sylow_normalizes_components hcoreH P hvz hvzS hL.2
    have h2 : v ∈ (Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype :=
      ⟨_, hnorm, rfl⟩
    rw [map_subtype_normalizer hL.1] at h2
    exact h2.2
  obtain ⟨z, hzV, hzT, hz1⟩ : ∃ z ∈ V, z ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ z ≠ 1 := by
    have hT2 : IsPGroup 2 T := h.sylow.1
    have : Group.IsNilpotent T := hT2.isNilpotent
    have hnormal : (V.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h.normal
    have hne : V.subgroupOf T ≠ ⊥ := by
      intro h0
      apply h.ne_bot
      rw [← Subgroup.map_subgroupOf_eq_of_le h.le, h0, Subgroup.map_bot]
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    refine ⟨y, hy.1, ⟨y.2, Subgroup.mem_centralizer_iff.2 fun t ht =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)⟩, fun h1 => hy1 ?_⟩
    exact Subtype.ext (Subtype.ext h1)
  have hz2 : z ^ 2 = 1 := h.isElemAbelian.2 z hzV
  have hZ2 : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (z ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hCz : Subgroup.centralizer ({z} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    ext g
    constructor
    · intro hg
      have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.1 hg
      have hgZ : g ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨k, rfl⟩
        exact ((Commute.zpow_left hgz.symm k).symm).eq.symm
      exact ⟨Subgroup.centralizer_le_normalizer _ hgZ, hgZ⟩
    · rintro ⟨-, hg⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hg z (Subgroup.mem_zpowers z)).symm
  have hTsyl : IsSylowTwoOf T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hZT : Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
    intro h0
    apply hz1
    have : z ∈ Subgroup.zpowers z ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) :=
      ⟨Subgroup.mem_zpowers z, hzT⟩
    rw [h0] at this
    exact this
  have hNz := CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hTsyl hZ2 hZT
  have hCz2 : CharTwo (Subgroup.centralizer ({z} : Set G)) := by
    rw [hCz]
    exact CT.CharTwo.inf_centralizer hNz Subgroup.le_normalizer hZ2
  have hzQ : z ∈ Q := hVQ hzV
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hUz : U ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer ({z} : Set G)) := by
    refine C1.le_pCoreOf_of_normalized (le_inf (fun u hu => ?_) (fun u hu => ?_)) (fun g hg => ?_)
      (h.isPGroup_V.to_le hUV)
    · exact Subgroup.mem_centralizer_iff.2 fun u' hu' => hVc _ (hUV hu') _ (hUV hu)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hVc _ (hUV hu) _ hzV)
    · exact Subgroup.centralizer_le_normalizer _ hg.1
  have h115 : Lemma115Hyp H Q (Subgroup.centralizer ({z} : Set G)) z :=
    { pCore_ne_bot := fun h0 => hU.2.1 (le_bot_iff.1 (h0 ▸ (C1.le_pCoreOf_of_normalized
        (fun u hu => Subgroup.mem_centralizer_iff.2 fun u' hu' => hVc _ (hUV hu') _ (hUV hu))
        (Subgroup.centralizer_le_normalizer _) (h.isPGroup_V.to_le hUV))))
      sylow := hQH
      charTwo := hCz2
      pCore_M_ne_bot := fun h0 => hz1 (by
        have hle : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
          C1.le_pCoreOf_of_normalized (Subgroup.zpowers_le.2 hzC) (by
            rw [hCz]; exact inf_le_left) hZ2
        have := hle (Subgroup.mem_zpowers z)
        rw [h0] at this
        exact this)
      le := fun q hq => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hQV hq) z hzV).symm
      centralizer_le := fun g hg => Subgroup.centralizer_le hUz hg.2
      centralizer_z_le := le_rfl
      z_ne_one := hz1
      z_mem := hzQ
      z_central := Subgroup.mem_centralizer_iff.2 fun q hq =>
        (Subgroup.mem_centralizer_iff.1 (hQV hq) z hzV).symm
      z_sq := hz2 }
  obtain ⟨-, -, -, hcases⟩ := Lemma115_3_List.component_cases hlist h.simple h.nonabelian
    (qtkeCore_of_cat h.nonabelian h.qtke) h115 hL
  set R := Q ⊓ Subgroup.normalizer (L : Set G) with hRdef
  have hRL : R ⊓ L = Q ⊓ L := by
    rw [hRdef, inf_assoc, inf_eq_right.2 (Subgroup.le_normalizer : L ≤ _)]
  have hE : E68Hyp L V R z :=
    { quasisimple := hLq
      elemAbelian := h.isElemAbelian
      mem := hzV
      isPGroup := hQ2.to_le inf_le_left
      le := le_inf hVQ hVN
      centralizer := inf_le_left.trans hQV
      normalizer := inf_le_right
      sylow := hRL ▸ hSL
      four_le := by
        rw [hidx]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hn
      centralizes := by
        intro a ha haL y hyL hya hy2
        obtain ⟨k, hk⟩ := hy2
        have haU : a ∉ U := fun haU => haL (hUC haU).2
        have hUW : U < U ⊔ Subgroup.zpowers a :=
          lt_of_le_of_ne le_sup_left fun he =>
            haU (he ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
        have hWV : U ⊔ Subgroup.zpowers a ≤ V := sup_le hUV (Subgroup.zpowers_le.2 ha)
        have hyW : y ∈ Subgroup.centralizer ((U ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
          have hle : U ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({y} : Set G) := by
            refine sup_le (fun u hu => ?_) (Subgroup.zpowers_le.2 ?_)
            · exact Subgroup.mem_centralizer_singleton_iff.2
                (Subgroup.mem_centralizer_iff.1 (hLH hyL) u hu)
            · exact Subgroup.mem_centralizer_singleton_iff.2 hya.symm
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hw))
        have hyM : y ∈ M := hmax _ hUW hWV hyW
        have hyR : y ∈ twoPrimeResidual (M ⊓ Subgroup.centralizer (U : Set G)) :=
          mem_twoPrimeResidual_of_pow' ⟨hyM, hLH hyL⟩ hk
        exact (hU.2.2.2 hyR).2 }
  obtain ⟨x, hxL, hxodd, hxR, hximp⟩ := hE68 G L V R z hcases hE
  have : Fintype ↥Q := Fintype.ofFinite _
  set O : Finset (Subgroup G) :=
    Finset.univ.image (fun q : ↥Q => CFSG.conjugate L (q : G)⁻¹) with hOdef
  have hmemO : ∀ K : Subgroup G, K ∈ O ↔ ∃ q ∈ Q, K = CFSG.conjugate L q⁻¹ := by
    intro K
    rw [hOdef, Finset.mem_image]
    constructor
    · rintro ⟨q, -, rfl⟩
      exact ⟨q, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, Finset.mem_univ _, rfl⟩
  have hLO : L ∈ O := (hmemO L).2 ⟨1, Q.one_mem, by
    ext y
    rw [mem_conjugate_iff']
    simp⟩
  have hcomp : ∀ K ∈ O, IsComponentIn K H := by
    intro K hK
    obtain ⟨q, hq, rfl⟩ := (hmemO K).1 hK
    exact Unc25G2.isComponentIn_conjugate hL (H.inv_mem (hQH' hq))
  have hcommK : ∀ K₁ ∈ O, ∀ K₂ ∈ O, K₁ ≠ K₂ → ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
    intro K₁ hK₁ K₂ hK₂ hne a ha b hb
    rcases BenderBranch.eq_or_commute_of_isComponentIn (hcomp K₁ hK₁) (hcomp K₂ hK₂) with
      h1 | h1
    · exact absurd h1 hne
    · have h2 := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1) ha
      exact (Subgroup.mem_centralizer_iff.1 h2 b hb).symm
  have hrep : ∀ K : Subgroup G, ∃ q : G, K ∈ O → q ∈ Q ∧ K = CFSG.conjugate L q⁻¹ ∧
      (K = L → q = 1) := by
    intro K
    by_cases hKL : K = L
    · refine ⟨1, fun _ => ⟨Q.one_mem, ?_, fun _ => rfl⟩⟩
      rw [hKL]
      ext y
      rw [mem_conjugate_iff']
      simp
    · by_cases hK : K ∈ O
      · obtain ⟨q, hq, hKq⟩ := (hmemO K).1 hK
        exact ⟨q, fun _ => ⟨hq, hKq, fun h' => absurd h' hKL⟩⟩
      · exact ⟨1, fun h' => absurd h' hK⟩
  choose rep hrep using hrep
  have hmemconj : ∀ (q y : G), y ∈ CFSG.conjugate L q⁻¹ ↔ q⁻¹ * y * q ∈ L := by
    intro q y
    rw [mem_conjugate_iff', inv_inv]
  set f : Subgroup G → G := fun K => rep K * x * (rep K)⁻¹ with hfdef
  have hfK : ∀ K ∈ O, f K ∈ K := by
    intro K hK
    obtain ⟨-, hKq, -⟩ := hrep K hK
    have h1 : f K ∈ CFSG.conjugate L (rep K)⁻¹ := by
      rw [hmemconj]
      have e1 : (rep K)⁻¹ * f K * rep K = x := by
        simp only [hfdef]
        group
      rw [e1]
      exact hxL
    exact (SetLike.ext_iff.1 hKq (f K)).2 h1
  have hfcomm : (O : Set (Subgroup G)).Pairwise (Commute on f) := by
    intro K₁ hK₁ K₂ hK₂ hne
    exact hcommK K₁ hK₁ K₂ hK₂ hne _ (hfK K₁ hK₁) _ (hfK K₂ hK₂)
  set x' := O.noncommProd f hfcomm with hx'def
  have hfL : f L = x := by
    have h1 := (hrep L hLO).2.2 rfl
    simp [hfdef, h1]
  set c := (O.erase L).noncommProd f
    (fun _ hx _ hy hxy => hfcomm (O.mem_of_mem_erase hx) (O.mem_of_mem_erase hy) hxy) with hcdef
  have hx'c : x' = x * c := by
    rw [hx'def, ← Finset.mul_noncommProd_erase O hLO f hfcomm, hfL]
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := by
    refine Finset.noncommProd_induction _ _ _ (· ∈ Subgroup.centralizer (L : Set G))
      (fun _ _ ha hb => Subgroup.mul_mem _ ha hb) (Subgroup.one_mem _) ?_
    intro K hK
    have hKO := O.mem_of_mem_erase hK
    have hKL : K ≠ L := Finset.ne_of_mem_erase hK
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact hcommK L hLO K hKO hKL.symm l hl _ (hfK K hKO)
  have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.1 hcC x hxL
  have hx'H : x' ∈ H := by
    refine Finset.noncommProd_induction _ _ _ (· ∈ H) (fun _ _ ha hb => H.mul_mem ha hb)
      H.one_mem ?_
    intro K hK
    exact (hcomp K hK).1 (hfK K hK)
  have hx'o : x' ^ orderOf x = 1 := by
    rw [hx'def, noncommProd_pow' O f hfcomm (orderOf x) (fun K₁ hK₁ K₂ hK₂ hne =>
      ((hfcomm hK₁ hK₂ hne).pow_left _).pow_right _)]
    refine Finset.noncommProd_induction _ _ _ (· = 1) (fun _ _ ha hb => by rw [ha, hb, one_mul])
      rfl ?_
    intro K _
    show (rep K * x * (rep K)⁻¹) ^ orderOf x = 1
    rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hconjconj : ∀ (a b : G), CFSG.conjugate (CFSG.conjugate L a⁻¹) b⁻¹ =
      CFSG.conjugate L (b * a)⁻¹ := by
    intro a b
    ext y
    have e1 : a⁻¹ * (b⁻¹ * y * b⁻¹⁻¹) * a = (b * a)⁻¹ * y * (b * a) := by group
    rw [mem_conjugate_iff', hmemconj a, hmemconj (b * a), e1]
  have hconjQ : ∀ q ∈ Q, q * x' * q⁻¹ * x'⁻¹ ∈ Q := by
    intro q hq
    let e : Subgroup G ≃ Subgroup G :=
      { toFun := fun K => CFSG.conjugate K q⁻¹
        invFun := fun K => CFSG.conjugate K q
        left_inv := fun K => by
          ext y
          show y ∈ CFSG.conjugate (CFSG.conjugate K q⁻¹) q ↔ y ∈ K
          rw [mem_conjugate_iff', mem_conjugate_iff']
          constructor <;> intro hy <;> simpa [mul_assoc] using hy
        right_inv := fun K => by
          ext y
          show y ∈ CFSG.conjugate (CFSG.conjugate K q) q⁻¹ ↔ y ∈ K
          rw [mem_conjugate_iff', mem_conjugate_iff']
          constructor <;> intro hy <;> simpa [mul_assoc] using hy }
    have he : ∀ K, e K = CFSG.conjugate K q⁻¹ := fun K => rfl
    have heO : ∀ K, K ∈ O ↔ e K ∈ O := by
      intro K
      constructor
      · intro hK
        obtain ⟨r, hr, rfl⟩ := (hmemO K).1 hK
        rw [he, hconjconj]
        exact (hmemO _).2 ⟨q * r, Q.mul_mem hq hr, rfl⟩
      · intro hK
        rw [he] at hK
        obtain ⟨r, hr, hKr⟩ := (hmemO _).1 hK
        refine (hmemO K).2 ⟨q⁻¹ * r, Q.mul_mem (Q.inv_mem hq) hr, ?_⟩
        have h1 : CFSG.conjugate (CFSG.conjugate K q⁻¹) q = K := e.left_inv K
        rw [← h1, hKr]
        have h2 := hconjconj r q⁻¹
        rw [inv_inv] at h2
        rw [h2]
    have hσ : ∀ K ∈ O, q * f K * q⁻¹ * (f (e K))⁻¹ ∈ Q ∧
        q * f K * q⁻¹ * (f (e K))⁻¹ ∈ e K := by
      intro K hK
      have heK : e K ∈ O := (heO K).1 hK
      obtain ⟨ha, hKa, -⟩ := hrep K hK
      obtain ⟨hb, hKb, -⟩ := hrep (e K) heK
      obtain ⟨a, hadef⟩ : ∃ a, a = rep K := ⟨_, rfl⟩
      obtain ⟨b, hbdef⟩ : ∃ b, b = rep (e K) := ⟨_, rfl⟩
      rw [← hadef] at ha hKa
      rw [← hbdef] at hb hKb
      have hfKa : f K = a * x * a⁻¹ := by rw [hadef]
      have hfKb : f (e K) = b * x * b⁻¹ := by rw [hbdef]
      have hLab : CFSG.conjugate L (q * a)⁻¹ = CFSG.conjugate L b⁻¹ := by
        have h1 : CFSG.conjugate L (q * a)⁻¹ = e K := by
          rw [he, hKa, hconjconj]
        exact h1.trans hKb
      have hr : b⁻¹ * q * a ∈ R := by
        refine ⟨Q.mul_mem (Q.mul_mem (Q.inv_mem hb) hq) ha, ?_⟩
        show b⁻¹ * q * a ∈ Subgroup.normalizer (L : Set G)
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h2 := SetLike.ext_iff.1 hLab ((q * a) * y * (q * a)⁻¹)
        rw [hmemconj, hmemconj] at h2
        have e3 : (q * a)⁻¹ * ((q * a) * y * (q * a)⁻¹) * (q * a) = y := by group
        have e4 : b⁻¹ * ((q * a) * y * (q * a)⁻¹) * b =
            (b⁻¹ * q * a) * y * (b⁻¹ * q * a)⁻¹ := by group
        rw [e3, e4] at h2
        exact h2
      have hs : (b⁻¹ * q * a) * x * (b⁻¹ * q * a)⁻¹ * x⁻¹ ∈ R := by
        have := R.inv_mem (hxR _ hr)
        have e1 : (x * (b⁻¹ * q * a) * x⁻¹ * (b⁻¹ * q * a)⁻¹)⁻¹ =
            (b⁻¹ * q * a) * x * (b⁻¹ * q * a)⁻¹ * x⁻¹ := by group
        rwa [e1] at this
      have hsL : (b⁻¹ * q * a) * x * (b⁻¹ * q * a)⁻¹ * x⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.1 hr.2 x).1 hxL) (L.inv_mem hxL)
      have e1 : q * f K * q⁻¹ * (f (e K))⁻¹ =
          b * ((b⁻¹ * q * a) * x * (b⁻¹ * q * a)⁻¹ * x⁻¹) * b⁻¹ := by
        rw [hfKa, hfKb]
        group
      rw [e1]
      refine ⟨Q.mul_mem (Q.mul_mem hb hs.1) (Q.inv_mem hb), ?_⟩
      refine (SetLike.ext_iff.1 hKb _).2 ?_
      rw [hmemconj]
      have e2 : b⁻¹ * (b * ((b⁻¹ * q * a) * x * (b⁻¹ * q * a)⁻¹ * x⁻¹) * b⁻¹) * b =
          (b⁻¹ * q * a) * x * (b⁻¹ * q * a)⁻¹ * x⁻¹ := by group
      rw [e2]
      exact hsL
    set σ : Subgroup G → G := fun K => q * f (e.symm K) * q⁻¹ * (f K)⁻¹ with hσdef
    have hσK : ∀ K ∈ O, σ K ∈ Q ∧ σ K ∈ K := by
      intro K hK
      have hK' : e.symm K ∈ O := by
        rw [heO, Equiv.apply_symm_apply]
        exact hK
      have := hσ (e.symm K) hK'
      rw [Equiv.apply_symm_apply] at this
      exact this
    have hσcomm : (O : Set (Subgroup G)).Pairwise (Commute on σ) := by
      intro K₁ hK₁ K₂ hK₂ hne
      exact hcommK K₁ hK₁ K₂ hK₂ hne _ (hσK K₁ hK₁).2 _ (hσK K₂ hK₂).2
    have hσf : (O : Set (Subgroup G)).Pairwise fun K₁ K₂ => Commute (f K₁) (σ K₂) := by
      intro K₁ hK₁ K₂ hK₂ hne
      exact hcommK K₁ hK₁ K₂ hK₂ hne _ (hfK K₁ hK₁) _ (hσK K₂ hK₂).2
    have hcommσf := Finset.noncommProd_mul_distrib_aux hσcomm hfcomm hσf
    have hqcomm : (O : Set (Subgroup G)).Pairwise (Commute on fun K => q * f K * q⁻¹) :=
      fun K₁ hK₁ K₂ hK₂ hne => (hfcomm hK₁ hK₂ hne).conj q
    have hstep1 : q * x' * q⁻¹ = O.noncommProd (fun K => q * f K * q⁻¹) hqcomm := by
      have := Finset.map_noncommProd O f hfcomm (MulAut.conj q)
      simpa [MulAut.conj_apply, hx'def] using this
    have hcomp' : (O : Set (Subgroup G)).Pairwise (Commute on ((σ * f) ∘ e)) := by
      intro K₁ hK₁ K₂ hK₂ hne
      exact hcommσf ((heO K₁).1 hK₁) ((heO K₂).1 hK₂) (fun h' => hne (e.injective h'))
    have hstep2 : O.noncommProd (fun K => q * f K * q⁻¹) hqcomm =
        O.noncommProd (σ * f) hcommσf := by
      rw [← noncommProd_comp_equiv O e heO (σ * f) hcommσf hcomp']
      refine Finset.noncommProd_congr rfl (fun K hK => ?_) _
      show q * f K * q⁻¹ = (σ * f) (e K)
      simp only [Pi.mul_apply, hσdef, Equiv.symm_apply_apply]
      group
    rw [hstep1, hstep2, Finset.noncommProd_mul_distrib σ f hσcomm hfcomm hσf, ← hx'def,
      mul_inv_cancel_right]
    exact Finset.noncommProd_induction _ _ _ (· ∈ Q) (fun _ _ ha hb => Q.mul_mem ha hb)
      Q.one_mem fun K hK => (hσK K hK).1
  have hx'N : x' ∈ Subgroup.normalizer (Q : Set G) := by
    have hle : Q.map (MulAut.conj x').toMonoidHom ≤ Q := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hconjQ y⁻¹ (Q.inv_mem hy)
      have e1 : (MulAut.conj x').toMonoidHom y = y * (y⁻¹ * x' * y⁻¹⁻¹ * x'⁻¹) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e1]
      exact Q.mul_mem hy h1
    have heq : Q.map (MulAut.conj x').toMonoidHom = Q :=
      Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj x').injective).ge
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq
  have hx'M : x' ∈ M := h.normalizer_Q_le hx'N
  have hx'V : x' ∈ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2 ⟨hx'H, hx'M⟩
  have hxNL : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hxL
  have hVNL : ∀ a ∈ V, ∀ g ∈ Subgroup.centralizer (L : Set G),
      a * g * a⁻¹ ∈ Subgroup.centralizer (L : Set G) := fun a ha g hg =>
    conj_mem_centralizer_of_mem_normalizer (hVN a ha) hg
  have hxV : ∀ a ∈ V, ∃ b ∈ V, x * a * x⁻¹ * b⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha
    refine ⟨x' * a * x'⁻¹, (Subgroup.mem_normalizer_iff.1 hx'V a).1 ha, ?_⟩
    have e1 : x * a * x⁻¹ * (x' * a * x'⁻¹)⁻¹ = x * (a * c * a⁻¹ * c⁻¹) * x⁻¹ := by
      rw [hx'c]
      group
    rw [e1]
    exact conj_mem_centralizer_of_mem_normalizer hxNL
      (Subgroup.mul_mem _ (hVNL a ha c hcC) (Subgroup.inv_mem _ hcC))
  have hord := hximp hxV
  rw [hidx] at hord
  have hpow : ∀ j : ℕ, x' ^ j = x ^ j * c ^ j := fun j => by
    rw [hx'c]
    exact Commute.mul_pow hxc j
  have hcj : ∀ j : ℕ, c ^ j ∈ Subgroup.centralizer (L : Set G) := fun j => Subgroup.pow_mem _ hcC j
  have hagree : ∀ j : ℕ, ∀ a ∈ V, x' ^ j * a * (x' ^ j)⁻¹ * (x ^ j * a * (x ^ j)⁻¹)⁻¹ ∈
      Subgroup.centralizer (L : Set G) := by
    intro j a ha
    have e1 : x' ^ j * a * (x' ^ j)⁻¹ * (x ^ j * a * (x ^ j)⁻¹)⁻¹ =
        x ^ j * (c ^ j * (a * (c ^ j)⁻¹ * a⁻¹)) * (x ^ j)⁻¹ := by
      rw [hpow]
      group
    rw [e1]
    exact conj_mem_centralizer_of_mem_normalizer (Subgroup.pow_mem _ hxNL j)
      (Subgroup.mul_mem _ (hcj j) (hVNL a ha _ (Subgroup.inv_mem _ (hcj j))))
  refine ⟨x', ⟨hx'M, hx'H⟩, fun j => ?_⟩
  rw [← hord j]
  constructor
  · intro hj a ha
    have h1 := hagree j a ha
    have h2 : x' ^ j * a * (x' ^ j)⁻¹ = a := by
      rw [← Subgroup.mem_centralizer_iff.1 hj a ha, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 := Subgroup.inv_mem _ h1
    have e3 : (a * (x ^ j * a * (x ^ j)⁻¹)⁻¹)⁻¹ = x ^ j * a * (x ^ j)⁻¹ * a⁻¹ := by group
    rw [e3] at h3
    exact h3
  · intro hj
    refine mem_centralizer_of_odd h.isElemAbelian hUV hxodd ?_ (fun u hu => ?_) (fun a ha => ?_)
    · rw [← pow_mul, mul_comm, pow_mul, hx'o, one_pow]
    · exact (Subgroup.mem_centralizer_iff.1 (Subgroup.pow_mem _ hx'H j) u hu).symm
    · rw [← hCV]
      refine ⟨?_, ?_⟩
      · exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hx'V j) a).1 ha)
          (V.inv_mem ha)
      · have h1 := hagree j a ha
        have h2 := hj a ha
        have e1 : x' ^ j * a * (x' ^ j)⁻¹ * a⁻¹ =
            (x' ^ j * a * (x' ^ j)⁻¹ * (x ^ j * a * (x ^ j)⁻¹)⁻¹) *
              (x ^ j * a * (x ^ j)⁻¹ * a⁻¹) := by group
        rw [e1]
        exact Subgroup.mul_mem _ h1 h2

end E6
end CFSG.Quasithin
