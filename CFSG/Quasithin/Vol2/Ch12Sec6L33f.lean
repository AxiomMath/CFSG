module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33d
public import CFSG.Quasithin.Vol2.Ch12Sec6L33e
public import CFSG.Quasithin.Vol2.Ch12Sec6L33Claim
public import CFSG.Quasithin.Vol2.Ch12Sec6L24b
public import CFSG.Quasithin.Vol2.Ch12Sec6L33b

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P S126E
  S126L24 F126 Equiv

variable {G : Type} [Group G] [Finite G]

section Count

theorem factorization_two_eq {n k : ℕ} (hn : n ≠ 0) (h1 : 2 ^ k ∣ n) (h2 : ¬ 2 ^ (k + 1) ∣ n) :
    n.factorization 2 = k := by
  have a := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).1 h1
  have b : ¬ k + 1 ≤ n.factorization 2 := fun hb =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).2 hb)
  omega

theorem card_star_of_sylow {T H : Subgroup G} (hT : IsSylowTwoOf T H) :
    Nat.card (S126.star H T) = 2 ^ (Nat.card (S126.HStar H)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 ↥H :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).toSylow hT.2.2
  exact (T'.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H))).card_eq_multiplicity

theorem card_inf_eq_sixteen {Q : Type*} [Group Q] [Finite Q] {P N : Subgroup Q} [N.Normal]
    (hP : Nat.card P = 2 ^ (Nat.card Q).factorization 2) (hN : Nat.card N = 3600)
    (hQ : Nat.card Q = 14400 ∨ Nat.card Q = 28800) : Nat.card ↥(P ⊓ N) = 16 := by
  have hPp : IsPGroup 2 ↥P := IsPGroup.of_card hP
  obtain ⟨k, hk⟩ := (hPp.to_le (inf_le_left : P ⊓ N ≤ P)).exists_card_eq
  have hk4 : k ≤ 4 := by
    by_contra h5
    have h1 : 2 ^ 5 ∣ Nat.card ↥(P ⊓ N) := by
      rw [hk]
      exact pow_dvd_pow 2 (by omega)
    have h2 := h1.trans (Subgroup.card_dvd_of_le (inf_le_right : P ⊓ N ≤ N))
    rw [hN] at h2
    norm_num at h2
  have hmul : Nat.card ↥(P ⊓ N) * N.relIndex P = Nat.card P := by
    have h := Subgroup.relIndex_mul_relIndex ⊥ (P ⊓ N) P bot_le inf_le_left
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
      Subgroup.inf_relIndex_left] at h
    exact h
  have hdvd : N.relIndex P ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N P
  have hidx := N.card_mul_index
  rw [hN] at hidx
  rcases hQ with hQ | hQ
  · have hf : (Nat.card Q).factorization 2 = 6 :=
      factorization_two_eq (by omega) (by rw [hQ]; norm_num) (by rw [hQ]; norm_num)
    rw [hf] at hP
    rw [hQ] at hidx
    have hi : N.index = 4 := by omega
    rw [hi] at hdvd
    have hr := Nat.le_of_dvd (by norm_num) hdvd
    rw [hk, hP] at hmul
    rw [hk]
    interval_cases k <;> omega
  · have hf : (Nat.card Q).factorization 2 = 7 :=
      factorization_two_eq (by omega) (by rw [hQ]; norm_num) (by rw [hQ]; norm_num)
    rw [hf] at hP
    rw [hQ] at hidx
    have hi : N.index = 8 := by omega
    rw [hi] at hdvd
    have hr := Nat.le_of_dvd (by norm_num) hdvd
    rw [hk, hP] at hmul
    rw [hk]
    interval_cases k <;> omega

end Count

section Fix

variable {T L V H K : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem le_normalizer_of_conj {Q : Type*} [Group Q] {Y S : Subgroup Q}
    (h : ∀ y ∈ Y, ∀ z ∈ S, y * z * y⁻¹ ∈ S) : Y ≤ Subgroup.normalizer (S : Set Q) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨h y hy z, fun hz => ?_⟩
  have := h y⁻¹ (Y.inv_mem hy) _ hz
  simpa [mul_assoc] using this

theorem mem_E16_of_conj (F : Frame126 T L V) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    {r : G} (hrT : r ∈ T)
    (hc : ∀ l ∈ Li L F.V1, l ∈ Subgroup.normalizer (V : Set G) → l * r * l⁻¹ * r⁻¹ ∈ T)
    {σ : Perm (Fin 8)} (hσ : ActsAs F r σ) : σ ∈ E16 := by
  have hrV := hTV hrT
  obtain ⟨σ', hσ'P, hσ'⟩ := actsAs_of_mem_T F hrT
  have hσP : PresPart σ := hσ'.unique hσ hrV ▸ hσ'P
  have key : ∀ c : Perm (Fin 8), c ∈ alternatingGroup (Fin 8) → c ^ 3 = 1 →
      (∀ i : Fin 8, (i.val < 4 ↔ (c i).val < 4)) → PresPart (c * σ * c⁻¹ * σ⁻¹) := by
    intro c hc' hc3 hcb
    obtain ⟨l, hlL1, hlV, hl⟩ := S126L1b.exists_mem_L1 F hc' hc3 hcb
    have hx := hc l hlL1 hlV
    obtain ⟨ρ, hρP, hρ⟩ := actsAs_of_mem_T F hx
    have h1 := hl.commutator hσ hlV hrV
    rw [hρ.unique h1 (hTV hx)] at hρP
    exact hρP
  exact eq_tau_of_comm hσP (key c1 c1_mem c1_pow_three c1_block)
    (key c2 c2_mem c2_pow_three c2_block)

theorem fix5_of_mem (F : Frame126 T L V) (h918 : HypF918 T V L F.V1 F.V5 H K)
    (h2 : Case2 T L H K) {s : S126.HStar H}
    (hs : s ∈ S126.star H T ⊓ S126.star H (conjClosure K T)) :
    Fix5 F.V1 F.V5 H (psiH h918.toHypF98.toHypF91 s) := by
  set h := h918.toHypF98.toHypF91 with hh
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans h.reduced.2.1
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVN : F.V5 ≤ N1 F.V1 := (le_conjClosure F.V5 H).trans hUN
  have hQT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le h.sylow_H
  set Ss := S126.star H T ⊓ S126.star H (conjClosure K T) with hSs
  have hK₀n : (S126.star H (conjClosure K T)).Normal := by
    have : ((conjClosure K T).subgroupOf H).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 (h918.K₀_normal g.2) n).1 hn⟩
    exact this.map _ (QuotientGroup.mk'_surjective _)
  have hMN : S126.star H (Subgroup.normalizer (L : Set G) ⊓ H) ≤
      Subgroup.normalizer (Ss : Set (S126.HStar H)) := by
    rw [h2.2.2.2.2.2]
    refine sup_le (le_normalizer_of_conj fun y hy z hz => ⟨?_, hK₀n.conj_mem z hz.2 y⟩)
      inf_le_right
    exact (S126.star H T).mul_mem ((S126.star H T).mul_mem hy hz.1) ((S126.star H T).inv_mem hy)
  have hconjT : ∀ l ∈ Li L F.V1, ∀ x : ↥H, (x : G) ∈ T →
      (QuotientGroup.mk x : S126.HStar H) ∈ Ss → l * x * l⁻¹ * (x : G)⁻¹ ∈ T := by
    intro l hl x hxT hx
    have hlH : l ∈ H := h.L₁T_le_H (Subgroup.mem_sup_left hl)
    have hlM : (QuotientGroup.mk ⟨l, hlH⟩ : S126.HStar H) ∈
        S126.star H (Subgroup.normalizer (L : Set G) ⊓ H) :=
      ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.2 ⟨Subgroup.le_normalizer (L1_le_L hl), hlH⟩, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hMN hlM) _).1 hx
    obtain ⟨y, hyT, hy⟩ := h1.1
    have hy' : (QuotientGroup.mk y : S126.HStar H) =
        QuotientGroup.mk (⟨l, hlH⟩ * x * ⟨l, hlH⟩⁻¹ : ↥H) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hy
    have h2 := hQT (mem_pCoreOf_of_mk_eq hy')
    have h3 : l * x * l⁻¹ ∈ T := by
      have := T.mul_mem (Subgroup.mem_subgroupOf.1 hyT) h2
      simpa [mul_assoc] using this
    exact T.mul_mem h3 (T.inv_mem hxT)
  obtain ⟨x, hxT, rfl⟩ := hs.1
  have hxT' : (x : G) ∈ T := Subgroup.mem_subgroupOf.1 hxT
  show Fix5 F.V1 F.V5 H (thetaH h x)
  rw [fix5_thetaH_iff h x hVN]
  obtain ⟨σ, -, hσ⟩ := actsAs_of_mem_T F hxT'
  have hE : σ ∈ E16 :=
    mem_E16_of_conj F hTV hxT' (fun l hl _ => hconjT l hl x hxT' hs) hσ
  have hc := mem_centralizerMod_of_E16 (hTV hxT') (h.T_normalizes_V₁ hxT') hσ hE
  intro v hv
  have hvV : v ∈ V := h.Vp_le_V hv
  have key : ∀ a ∈ V, a * v⁻¹ ∈ F.V1 → a⁻¹ * v ∈ F.V1 := fun a haV ha => by
    have e : a⁻¹ * v = (a * v⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact S126L1b.comm_of_mem (V.inv_mem haV) hvV
    rw [e]
    exact F.V1.inv_mem ha
  exact key _ (conj_mem (hTV hxT') ⟨v, hvV⟩) (hc.2.2 v hv)

end Fix

section Omega

variable {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem false_of_omega (F : Frame126 T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (h2 : Case2 T L H K)
    (hO : @Omega4PlusModule _ (commGroupOfElemAbelian h918.toHypF98.toHypF91.isElemAbelian_tilde)
      (autOn (tildeOf F.V1 (conjClosure K T)) (tildeOf F.V1 (conjClosure F.V5 H))) 2) :
    False := by
  set h := h918.toHypF98.toHypF91 with hh
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVN : F.V5 ≤ N1 F.V1 := (le_conjClosure F.V5 H).trans hUN
  have hK₀H : conjClosure K T ≤ H := by
    have e := h918.H_eq
    exact e ▸ le_sup_left
  obtain ⟨-, -, ⟨e₀⟩, -, hcardH, -⟩ := id h2
  have hc3600 : Nat.card ↥(S126.star H (conjClosure K T)) = 3600 := by
    rw [Nat.card_congr e₀.toEquiv, Nat.card_prod, S126.card_alternatingGroup_five]
  have hK₀n : (S126.star H (conjClosure K T)).Normal := by
    have : ((conjClosure K T).subgroupOf H).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 (h918.K₀_normal g.2) n).1 hn⟩
    exact this.map _ (QuotientGroup.mk'_surjective _)
  have hXs : ((conjClosure K T).subgroupOf H).map (thetaH h) =
      (S126.star H (conjClosure K T)).map (psiH h) := by
    rw [S126.star, Subgroup.map_map]
    rfl
  have hX : autOn (tildeOf F.V1 (conjClosure K T)) (UT F.V1 F.V5 H) =
      (S126.star H (conjClosure K T)).map (psiH h) := by
    rw [← range_thetaH h hK₀H, hXs]
  have hXc : Nat.card ↥(autOn (tildeOf F.V1 (conjClosure K T)) (UT F.V1 F.V5 H)) = 3600 := by
    rw [hX, Subgroup.card_map_of_injective (psiH_injective h), hc3600]
  have hSc : Nat.card ↥(S126.star H T ⊓ S126.star H (conjClosure K T)) = 16 :=
    card_inf_eq_sixteen (card_star_of_sylow h.sylow_H) hc3600 hcardH
  set S := (S126.star H T ⊓ S126.star H (conjClosure K T)).map (psiH h) with hS
  have hSX : S ≤ autOn (tildeOf F.V1 (conjClosure K T)) (UT F.V1 F.V5 H) := by
    rw [hX]
    exact Subgroup.map_mono inf_le_right
  have hS16 : Nat.card S = 16 := by
    rw [hS, Subgroup.card_map_of_injective (psiH_injective h), hSc]
  have hup : Nat.card {w : ↥(UT F.V1 F.V5 H) // ∀ f ∈ S, f w = w} ≤ 4 :=
    @card_fix_le_of_omega4 _ (commGroupOfElemAbelian h.isElemAbelian_tilde) _ S hXc hO hSX hS16
  have h16 : Nat.card ↥(tildeOf F.V1 F.V5) = 16 := by
    have h1 : Nat.card ↥(tildeOf F.V1 F.V5) = F.V1.relIndex F.V5 := by
      have := relIndex_secImg (A := N1 F.V1) (B := F.V1) (T := F.V1) (H := F.V5) le_rfl
        h.V₁_le_Vp hVN
      rw [show secImg (N1 F.V1) F.V1 F.V1 = ⊥ from tildeOf_eq_bot_of_le le_rfl,
        Subgroup.relIndex_bot_left] at this
      exact this
    have h2 := Subgroup.relIndex_mul_relIndex ⊥ F.V1 F.V5 bot_le h.V₁_le_Vp
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, h.card_V₁,
      card_V5 (beta_injective F hZ)] at h2
    omega
  have hlow : 16 ≤ Nat.card {w : ↥(UT F.V1 F.V5 H) // ∀ f ∈ S, f w = w} := by
    rw [← h16]
    refine Nat.card_le_card_of_injective
      (fun x => ⟨⟨x, secImg_mono (le_conjClosure F.V5 H) x.2⟩, fun f hf => ?_⟩) ?_
    · obtain ⟨s, hs, rfl⟩ := hf
      exact fix5_of_mem F h918 h2 hs _ x.2
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z => ((z.1 : ↥(UT F.V1 F.V5 H)) :
        SecQuot (N1 F.V1) F.V1)) hxy)
  omega

end Omega

section Main

variable {T L V H K : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem not_case1 (e : Nonempty (↥(S126.star H K) ≃* alternatingGroup (Fin 5)))
    (h1 : Case1 T L H K) : False := by
  obtain ⟨e⟩ := e
  have h60 : Nat.card ↥(S126.star H K) = 60 := by
    rw [Nat.card_congr e.toEquiv, S126.card_alternatingGroup_five]
  rcases h1.2.1 with ⟨F, _, _, hF, ⟨e₁⟩, -⟩ | ⟨F, _, _, hF, ⟨e₁⟩, -⟩
  · have hc : Nat.card (S126.PSL3Model F) = 20160 := by
      have := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 3)
        (by norm_num)
      rw [hF] at this
      exact this.trans (by decide)
    have := (Nat.card_congr e₁.toEquiv).symm.trans h60
    rw [hc] at this
    norm_num at this
  · have : Fintype F := Fintype.ofFinite F
    have hc : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 60480 := by
      rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
        Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hF, Fin.prod_univ_three]
      norm_num
    have := (Nat.card_congr e₁.toEquiv).symm.trans h60
    rw [hc] at this
    norm_num at this

theorem false_of_case2 (hab : Claim12_6_33ab) (h1262 : Theorem12_6_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K) (h2 : Case2 T L H K) :
    False := by
  obtain ⟨t, ht, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hall
    push Not at hall
    exact h2.1 (le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.1 (hall t ht) k).1 hk) (le_conjClosure K T))
  rcases hab G T L V F hH hZ H K hIs h2 h918 t ht htK with ⟨I, -, hIU, -, ha1, ha2⟩ | hb
  · exact false_of_comm_le F hH hIs h918 h2 h1262 ht htK
      (comm_le_of_claim_a h918 h2 ht htK hIU ha1 ha2)
  · exact false_of_omega F hZ h918 h2 hb

end Main

theorem lemma12_6_33_of (h30 : Lemma12_6_30) (h31 : Lemma12_6_31) (h32 : Lemma12_6_32)
    (h1262 : Theorem12_6_2) (hab : Claim12_6_33ab) : Lemma12_6_33 := by
  intro G _ _ T L V _ F hH hZ H K hIs
  have h918 := ((h30 G T L V F hH hZ).2 H K hIs).2.2
  rcases h31 G T L V F hH hZ H K hIs with h1 | h2 | h3
  · exact (not_case1 (h32 G T L V F hH hZ H K hIs) h1).elim
  · exact (false_of_case2 hab h1262 F hH hZ hIs h918 h2).elim
  · exact h3.1

end CFSG.Quasithin.H13.L1233
