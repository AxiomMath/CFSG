module

public import CFSG.Quasithin.H13.U3S1348A
public import CFSG.Quasithin.H13.U3BlocksR
public import CFSG.RankThree.SubgroupLists.CentralizerPerfect
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

theorem prime_dvd_six_pow {p s : ℕ} (hp : p.Prime) (h : p ∣ 6 ^ s) : p = 2 ∨ p = 3 := by
  have h6 : p ∣ 2 * 3 := hp.dvd_of_dvd_pow h
  rcases (Nat.Prime.dvd_mul hp).1 h6 with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)

theorem eq_three_pow_of_dvd_six_pow {a s : ℕ} (ha : a ∣ 6 ^ s) (hodd : Odd a) :
    ∃ b, a = 3 ^ b := by
  have hcop : Nat.Coprime a (2 ^ s) := Nat.Coprime.pow_right s (Odd.coprime_two_right hodd)
  have h3 : a ∣ 3 ^ s := by
    have e : 6 ^ s = 3 ^ s * 2 ^ s := by rw [← mul_pow]; norm_num
    rw [e] at ha
    exact hcop.dvd_of_dvd_mul_right ha
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h3
  exact ⟨b, hb⟩

theorem eq_two_of_card_sl2_dvd {q s : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (h : q * (q ^ 2 - 1) ∣ 6 ^ s) : q = 2 := by
  have hfac : q * (q ^ 2 - 1) = q * (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  rw [hfac] at h
  have hm : q - 1 ∣ 6 ^ s := (Dvd.intro (q * (q + 1)) (by ring)).trans h
  have hp : q + 1 ∣ 6 ^ s := (Dvd.intro_left (q * (q - 1)) rfl).trans h
  obtain ⟨k, hk⟩ := hqe
  have hmo : Odd (q - 1) := ⟨k - 1, by omega⟩
  have hpo : Odd (q + 1) := ⟨k, by omega⟩
  obtain ⟨c, hc⟩ := eq_three_pow_of_dvd_six_pow hm hmo
  obtain ⟨d, hd⟩ := eq_three_pow_of_dvd_six_pow hp hpo
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · rw [pow_zero] at hc
    omega
  · exfalso
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · rw [pow_zero] at hd
      omega
    · have h3c : 3 ∣ q - 1 := hc ▸ dvd_pow_self 3 hc0.ne'
      have h3d : 3 ∣ q + 1 := hd ▸ dvd_pow_self 3 hd0.ne'
      omega

theorem not_dvd_six_pow_sq_add {q s : ℕ} (hq2 : 2 ≤ q) (hqe : Even q) :
    ¬ q ^ 2 + q + 1 ∣ 6 ^ s := by
  intro h
  have hodd : Odd (q ^ 2 + q + 1) := by
    obtain ⟨k, rfl⟩ := hqe
    exact ⟨2 * k ^ 2 + k, by ring⟩
  obtain ⟨b, hb⟩ := eq_three_pow_of_dvd_six_pow h hodd
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    interval_cases b
    · rw [pow_zero] at hb
      nlinarith
    · rw [pow_one] at hb
      nlinarith
  have h9 : 9 ∣ q ^ 2 + q + 1 := by
    rw [hb]
    exact (pow_dvd_pow 3 hb2 : 3 ^ 2 ∣ 3 ^ b)
  have key : ∀ r : ℕ, r < 9 → (r ^ 2 + r + 1) % 9 ≠ 0 := by decide
  set r := q % 9 with hr
  set k := q / 9 with hkdef
  have hqk : q = 9 * k + r := (Nat.div_add_mod q 9).symm
  have e : q ^ 2 + q + 1 = 9 * (9 * k ^ 2 + 2 * k * r + k) + (r ^ 2 + r + 1) := by
    rw [hqk]
    ring
  rw [e] at h9
  have h9r : 9 ∣ r ^ 2 + r + 1 := (Nat.dvd_add_right (dvd_mul_right 9 _)).1 h9
  exact key r (Nat.mod_lt _ (by norm_num)) (Nat.mod_eq_zero_of_dvd h9r)

theorem card_eq_six_of_factorList {X : Type} [Group X] [Finite X] (h : B56FactorList X) {s : ℕ}
    (hd : Nat.card X ∣ 6 ^ s) : Nat.card X = 6 := by
  rcases h with ⟨n, K, _, _, hn, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, K, _, _, hm, -, hK, ⟨e⟩⟩
  · have hc : Nat.card X = Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, ← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv,
        CFSG.RankThree.SubgroupLists.card_sl2_field]
    rw [hc] at hd ⊢
    have hq2 : 2 ≤ Nat.card K := by
      rw [hK]
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hqe : Even (Nat.card K) := by
      rw [hK]
      exact Nat.even_pow.2 ⟨even_two, by omega⟩
    rw [eq_two_of_card_sl2_dvd hq2 hqe hd]
    norm_num
  · exfalso
    have hc : Nat.card X = 120 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [hc] at hd
    exact absurd (prime_dvd_six_pow Nat.prime_five ((by norm_num : 5 ∣ 120).trans hd))
      (by norm_num)
  · exfalso
    have hc : Nat.card X = Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three]
    have hq2 : 2 ≤ Nat.card K := by
      rw [hK]
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hqe : Even (Nat.card K) := by
      rw [hK]
      exact Nat.even_pow.2 ⟨even_two, by omega⟩
    apply not_dvd_six_pow_sq_add hq2 hqe (s := s)
    rw [hc] at hd
    refine dvd_trans ?_ hd
    have hfac : Nat.card K ^ 3 - 1 = (Nat.card K - 1) * (Nat.card K ^ 2 + Nat.card K + 1) := by
      have h1 : 1 ≤ Nat.card K := by omega
      have h3 : 1 ≤ Nat.card K ^ 3 := Nat.one_le_pow _ _ (by omega)
      zify [h1, h3]
      ring
    rw [hfac]
    exact (Dvd.intro_left (Nat.card K - 1) rfl).trans (Dvd.intro_left _ rfl)

theorem card_blocks_le_two (h56 : AsB56) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)} (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    {𝓗 I : Finset (Subgroup (MulAut W))}
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗) (hI : I ⊆ 𝓗)
    (hn : X ≤ normalizer ((⨆ L ∈ I, L : Subgroup (MulAut W)) : Set (MulAut W)))
    (hne : I.Nonempty)
    (hsec : ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (N : Subgroup Y) (_ : N.Normal),
      SQTKGroup Y ∧ Nonempty (↥(⨆ L ∈ I, L : Subgroup (MulAut W)) ≃* Y ⧸ N)) :
    I.card ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Gp : Subgroup (MulAut W) := ⨆ L ∈ I, L with hGp
  have hJX := B1.closure_transvectionsIn_le X
  have hGX : Gp ≤ X := iSup₂_le fun L hL => (hb.le_J (hI hL)).trans hJX
  have hcard : Nat.card Gp = 6 ^ I.card := by
    have h := hb.card_biSup_eq_prod (fun L => L) (fun L _ => le_rfl) I hI
    rw [Finset.prod_congr rfl fun L hL => hb.card_eq L (hI hL), Finset.prod_const] at h
    exact h
  have hsolvG : Group.IsSolvable ↥Gp := B1.solvable_of_le hGX hsolv
  have hO2G : pCoreOf 2 Gp = ⊥ := by
    have hQX : pCoreOf 2 Gp ≤ X := (pCoreOf_le 2 Gp).trans hGX
    refine hO2 _ hQX ((normal_subgroupOf_iff_le_normalizer hQX).2
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 Gp))) (pCoreOf_isPGroup 2 Gp)
  have hO2G' : ∀ Q : Subgroup (MulAut W), Q ≤ Gp → (Q.subgroupOf Gp).Normal →
      IsPGroup 2 Q → Q = ⊥ := fun Q hQ hQn hQ2 => by
    have := le_pCoreOf 2 hQ hQn hQ2
    rw [hO2G] at this
    exact le_bot_iff.1 this
  have hffJ : Gp = ffJ Gp := by
    refine le_antisymm (iSup₂_le fun L hL => ?_) (iSup₂_le fun A hA => hA.1)
    rw [← hb.closure_eq L (hI hL), Subgroup.closure_le]
    intro t ht
    have htG : t ∈ Gp := le_iSup₂_of_le (f := fun (K : Subgroup (MulAut W)) (_ : K ∈ I) => K)
      L hL le_rfl ht.1
    exact le_iSup₂_of_le (f := fun (A : Subgroup (MulAut W)) (_ : IsFFStarOffender Gp A) => A)
      (Subgroup.zpowers t) (B1.isFFStarOffender_zpowers hW hsolvG hO2G' htG ht.2) le_rfl
      (Subgroup.mem_zpowers t)
  have hGne : Gp ≠ ⊥ := by
    intro h
    have := hcard
    rw [h, card_bot] at this
    have h1 : 1 ≤ I.card := Finset.card_pos.2 hne
    have : 6 ≤ 6 ^ I.card := Nat.le_self_pow (by omega) 6
    omega
  have hdvd : ∀ K : Subgroup (MulAut W), K ≤ Gp → Nat.card K ∣ 6 ^ I.card := fun K hK =>
    hcard ▸ Subgroup.card_dvd_of_le hK
  rcases h56 W hW Gp hGne ⟨hO2G, hffJ, hsec⟩ with ⟨hqs, -⟩ | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hcomm, hf₁, hf₂, -⟩ | ⟨G₁, G₂, t, hG, -, -, ⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, -, -, -, ⟨e⟩, -⟩
  ·
    exfalso
    have hle := quasithinGenFitting_le Gp
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hqs
      (B1.solvable_of_le hle hsolvG)
  ·
    have h6 : Nat.card Gp = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [hcard] at h6
    have : I.card = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 6) (h6.trans (pow_one 6).symm)
    omega
  ·
    have h1 := card_eq_six_of_factorList hf₁ (hdvd G₁ (hsup ▸ le_sup_left))
    have h2 := card_eq_six_of_factorList hf₂ (hdvd G₂ (hsup ▸ le_sup_right))
    have hc := B2F.card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, card_bot, mul_one, hsup, h1, h2, hcard] at hc
    have : I.card = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 6) (hc.trans (by norm_num))
    omega
  ·
    exfalso
    have hG₁ : G₁ ≤ Gp := hG ▸ le_sup_left.trans le_sup_left
    have h360 : Nat.card G₁ = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have := hdvd G₁ hG₁
    rw [h360] at this
    exact absurd (prime_dvd_six_pow Nat.prime_five ((by norm_num : 5 ∣ 360).trans this))
      (by norm_num)
  ·
    exfalso
    have hG₁ : G₁ ≤ Gp := hsup ▸ le_sup_left
    have h168 : Nat.card G₁ = 168 := by
      rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, Nat.card_zmod]
      norm_num
    have := hdvd G₁ hG₁
    rw [h168] at this
    exact absurd (prime_dvd_six_pow (by norm_num : Nat.Prime 7)
      ((by norm_num : 7 ∣ 168).trans this)) (by norm_num)

theorem conjAut_autI_conjClosure {G : Type} [Group G] {V H R : Subgroup G}
    {hV : IsElemAbelian 2 V} {g : MulAut (IntMod V hV)} (hg : g ∈ autI hV H) :
    B1.conjAut g (autI hV (conjClosure (thompsonJ R) H)) =
      autI hV (conjClosure (thompsonJ R) H) := by
  obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hg
  rw [conjAut_eq_map, autI_cjSub hV y.2,
    B2F.cjSub_eq_of_mem_normalizer (le_normalizer_conjClosure _ H hy)]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_blocks (h56 : AsB56) (S : A6.Setting134 G T L V) {z : G} {H VH : Subgroup G}
    (hHz : InHz T L V z H) (hsolv : Group.IsSolvable ↥H) (hred : IsTwoReducedIn H VH)
    (hzL : z ∉ centralizer (L : Set G))
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G)) :
    ∃ (𝓗 I : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))),
      BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 I ∧ I.Nonempty ∧ I.card ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hV := hred.2.2.1 with hhV
  obtain ⟨hTsyl, -, hHz', hO2H, -⟩ := s134_inHz_facts S hHz
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  have hRH : r1Of T L V ≤ H := (r1Of_le_T T L V).trans hTsyl.1
  have hVR : VH ≤ r1Of T L V := (s134_VH_le_r1Of hred hcR).1.trans (s134_VH_le_r1Of hred hcR).2
  obtain ⟨𝓗, I, B⟩ := exists_blocksR (hV := hV) hred hsolv hVR hRH hJ
  set cc := conjClosure (thompsonJ (r1Of T L V)) H with hcc
  have hccH : cc ≤ H := conjClosure_le fun h hh j hj =>
    mul_mem (mul_mem hh (hRH ((iSup₂_le fun _ hA => hA.1 : thompsonJ (r1Of T L V) ≤ _) hj)))
      (inv_mem hh)
  have hccN : cc ≤ normalizer (VH : Set G) := hccH.trans hHN
  have hne : I.Nonempty := by
    by_contra hI
    rw [Finset.not_nonempty_iff_eq_empty] at hI
    have h1 : autI hV cc = ⊥ := by
      rw [B.eq, hI]
      simp
    exact hJ ((le_conjClosure _ H).trans ((autI_eq_bot_iff hV hccN).1 h1))
  refine ⟨𝓗, I, B, hne, ?_⟩
  have hX := B2F.isSolvable_autI hV hHN hsolv
  have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 =>
    B2F.eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
  have hn : autI hV H ≤ normalizer ((⨆ L ∈ I, L : Subgroup (MulAut (IntMod VH hV))) :
      Set (MulAut (IntMod VH hV))) := by
    rw [← B.eq]
    intro g hg
    refine E2.mem_normalizer_of_conjAut_le (conjAut_autI_conjClosure hg).le
      (conjAut_autI_conjClosure ((autI hV H).inv_mem hg)).le
  have hK := S.fsu.qtke
  have hccT : cc ≠ ⊤ := by
    intro htop
    have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem _)
    have hzc : ∀ g : G, g * z = z * g := fun g => by
      have hg : g ∈ centralizer ({z} : Set G) := hHz' (hccH (htop ▸ mem_top g))
      exact (mem_centralizer_singleton_iff.mp hg)
    have hcen : z ∈ center G := mem_center_iff.2 hzc
    have hbot : center G = ⊥ := by
      have := S.fsu.simple
      rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := S.fsu.nonabelian
        exact hab (mem_center_iff.1 (h ▸ mem_top b) a)
    rw [hbot, mem_bot] at hcen
    exact hz1 hcen
  have hsec : ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (N : Subgroup Y) (_ : N.Normal),
      SQTKGroup Y ∧ Nonempty (↥(⨆ L ∈ I, L : Subgroup (MulAut (IntMod VH hV))) ≃* Y ⧸ N) := by
    refine ⟨↥cc, inferInstance, inferInstance, (convHom hV cc hccN).ker, inferInstance,
      ⟨?_, kGroup_of_ne_top hK hccT⟩, ⟨?_⟩⟩
    · intro p hp hp2
      have : Fact p.Prime := ⟨hp⟩
      change CFSG.Open.pRank p (⊤ : Subgroup ↥cc) ≤ 2
      rw [pRank_top_subtype (p := p) cc]
      exact (CFSG.SectionRank.pRank_mono hp.one_lt hccH).trans
        (pRank_le_two_of_pCoreOf_ne_bot hK hO2H hp hp2)
    · exact (MulEquiv.subgroupCongr (B.eq.symm.trans (range_convHom hV cc hccN).symm)).trans
        (QuotientGroup.quotientKerEquivRange (convHom hV cc hccN)).symm
  exact card_blocks_le_two h56 (fun w => IntMod.sq_eq_one w) hX hO2 B.hb B.sub hn hne hsec

end CFSG.Quasithin.H13.U3
