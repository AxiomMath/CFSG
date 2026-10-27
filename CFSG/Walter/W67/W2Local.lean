module

public import CFSG.Walter.W67.W2Basic
public import CFSG.Walter.W67.Lemma26i
public import CFSG.Walter.W67.Transport

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_of_sylow {p : ℕ} [Fact p.Prime] {L : Subgroup G} (P Q : Sylow p G)
    (hP : (P : Subgroup G) ≤ L) (hQ : (Q : Subgroup G) ≤ L) :
    ∃ l ∈ L, ∀ y ∈ (Q : Subgroup G), l * y * l⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L (Q.subtype hQ) (P.subtype hP)
  refine ⟨l, l.2, fun y hy => ?_⟩
  have hy' : (⟨y, hQ hy⟩ : L) ∈ ((Q.subtype hQ : Sylow p L) : Subgroup L) := hy
  have := Subgroup.smul_mem_pointwise_smul (⟨y, hQ hy⟩ : L) (MulAut.conj l) _ hy'
  rw [← Sylow.coe_subgroup_smul, hl] at this
  exact this

theorem exists_mul_mem_normalizer {p : ℕ} [Fact p.Prime] {L M : Subgroup G}
    (hn : (L.subgroupOf M).Normal) (hLM : L ≤ M) (P : Sylow p G) (hPL : (P : Subgroup G) ≤ L)
    {x : G} (hx : x ∈ M) : ∃ l ∈ L, l * x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
  set Q := x • P
  have hQ : (Q : Subgroup G) ≤ L := by
    intro y hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hy' : x⁻¹ * y * x ∈ L := by
      have := hPL hy
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have h1 : x * (x⁻¹ * y * x) * x⁻¹ ∈ L := hn.conj_mem ⟨x⁻¹ * y * x, hLM hy'⟩ hy' ⟨x, hx⟩
    simpa [mul_assoc] using h1
  obtain ⟨l, hl, hlQ⟩ := exists_conj_le_of_sylow P Q hPL hQ
  refine ⟨l, hl, JT.mem_normalizer_of_conj_mem fun z hz => ?_⟩
  have hz' : x * z * x⁻¹ ∈ (Q : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul z (MulAut.conj x) (P : Subgroup G) hz
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have := hlQ _ hz'
  simpa [mul_assoc] using this

theorem le_normalizer_of_isSimpleGroup {L A : Subgroup G} (hLA : L ≤ A)
    (hn : (L.subgroupOf A).Normal) (hodd : Odd (L.subgroupOf A).index) [IsSimpleGroup L]
    {j : G} (hjL : j ∈ L) (hj1 : j ≠ 1) {k : ℕ} (hj : orderOf j = 2 ^ k) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  set s : Set G := {x | x ∈ A ∧ ∃ k : ℕ, orderOf x = 2 ^ k}
  set I := Subgroup.closure s
  have hIL : I ≤ L := (Subgroup.closure_le L).mpr fun x ⟨hxA, k, hk⟩ =>
    mem_of_odd_relIndex hn hodd hxA hk
  have hIN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (I : Set G) := by
    intro b hb
    refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
    have hmap : I.map (MulAut.conj b).toMonoidHom ≤ I := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨y, ⟨hyA, k, hk⟩, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hb y).mp hyA, k, ?_⟩
      change orderOf (b * y * b⁻¹) = 2 ^ k
      rw [orderOf_conj_mul, hk]
    exact hmap ⟨x, hx, rfl⟩
  have hLI : L ≤ I := by
    have hIn : (I.subgroupOf L).Normal := by
      refine ⟨fun x hx l => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hIN (Subgroup.le_normalizer (hLA l.2))) x).mp hx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (I.subgroupOf L) with hb | ht
    · exfalso
      have hjI : j ∈ I := Subgroup.subset_closure ⟨hLA hjL, k, hj⟩
      exact hj1 ((Subgroup.disjoint_def.mp (Subgroup.subgroupOf_eq_bot.mp hb)) hjI hjL)
    · exact Subgroup.subgroupOf_eq_top.mp ht
  rw [← le_antisymm hIL hLI]
  exact hIN

omit [Finite G] in
theorem commutatorElement_mul_mul {a b c d : G} (hbc : Commute b c) (hbd : Commute b d)
    (hda : Commute d a) : ⁅a * b, c * d⁆ = ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  have h1 : b * (c * d) * b⁻¹ = c * d := by rw [(hbc.mul_right hbd).eq, mul_inv_cancel_right]
  have h2 : d * a⁻¹ * d⁻¹ = a⁻¹ := by rw [hda.inv_right.eq, mul_inv_cancel_right]
  calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = a * (b * (c * d) * b⁻¹) * a⁻¹ * d⁻¹ * c⁻¹ := by
        group
    _ = a * c * (d * a⁻¹ * d⁻¹) * c⁻¹ := by rw [h1]; simp only [mul_assoc]
    _ = a * c * a⁻¹ * c⁻¹ := by rw [h2]

omit [Finite G] in
theorem commutator_zpowers_sup_le {j : G} {K' : Subgroup G}
    (hK' : K' ≤ Subgroup.centralizer ({j} : Set G)) :
    ⁅Subgroup.zpowers j ⊔ K', Subgroup.zpowers j ⊔ K'⁆ ≤ K' := by
  have hcomm : ∀ e ∈ Subgroup.zpowers j, ∀ k ∈ K', Commute e k := by
    intro e he k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact Commute.zpow_left
      (show Commute j k from (Subgroup.mem_centralizer_singleton_iff.mp (hK' hk)).symm) n
  have hN : Subgroup.zpowers j ≤ Subgroup.normalizer (K' : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K' : Set G))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK' hk)
  rw [sup_comm, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨k₁, hk₁, e₁, he₁, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hg₁
  obtain ⟨k₂, hk₂, e₂, he₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hg₂
  have he : Commute e₁ e₂ := by
    obtain ⟨n₁, rfl⟩ := Subgroup.mem_zpowers_iff.mp he₁
    obtain ⟨n₂, rfl⟩ := Subgroup.mem_zpowers_iff.mp he₂
    exact Commute.zpow_zpow_self j n₁ n₂
  rw [commutatorElement_mul_mul ((hcomm e₁ he₁ k₂ hk₂)) he ((hcomm e₂ he₂ k₁ hk₁))]
  exact K'.mul_mem (K'.mul_mem (K'.mul_mem hk₁ hk₂) (K'.inv_mem hk₁)) (K'.inv_mem hk₂)

namespace PSL2Sub

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {K : Subgroup X}

theorem mem_commutator_of_orderOf
    (e : K ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {x : X} (hxK : x ∈ K) {k : ℕ}
    (hx : orderOf x = 2 ^ k) : x ∈ ⁅K, K⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : IsPGroup 2 ((Subgroup.zpowers (⟨x, hxK⟩ : K))) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx])
  obtain ⟨Q, hQ⟩ := hW.exists_le_sylow
  set V := (Q : Subgroup K).map K.subtype
  have hVK : V ≤ K := Subgroup.map_subtype_le _
  have hV4 : Nat.card V = 4 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv, psl2_card_formula _ (isOddPrimePower_galoisField hp hf),
      GaloisField.card p f hf.ne', psl2_order_factorization_two_of_mod_eight h8]
    norm_num
  have hV := isKleinFour_of_card e hp hf h8 hVK hV4
  have hxV : x ∈ V := ⟨⟨x, hxK⟩, hQ (Subgroup.mem_zpowers _), rfl⟩
  exact le_commutator e hp hf h8 hVK hV le_rfl hxV

end PSL2Sub

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem E_le_normalizer_of_F_le
    {X : Subgroup G} (hXE : X ≤ fr.E) (hFX : h.F ≤ X) :
    fr.E ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨g, hgE, hg⟩ := fr.exists_generator_E
  have hFn := fr.F_normal_E
  have hN : Subgroup.zpowers g ≤ Subgroup.normalizer (h.F : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact Subgroup.mem_subgroupOf.mp
        (hFn.conj_mem ⟨y, fr.F_le_E hy⟩ hy ⟨g, hgE⟩)
    · intro hy
      have h1 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ ∈ h.F := Subgroup.mem_subgroupOf.mp
        (hFn.conj_mem ⟨g * y * g⁻¹, fr.F_le_E hy⟩ hy ⟨g⁻¹, fr.E.inv_mem hgE⟩)
      simpa [mul_assoc] using h1
  have hdec : ∀ e ∈ fr.E, ∃ c ∈ h.F, ∃ n : ℤ, c * g ^ n = e := by
    intro e he
    rw [← hg, sup_comm] at he
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ⟨c, hc, n, rfl⟩
  have hconjF : ∀ n : ℤ, ∀ c ∈ h.F, g ^ n * c * (g ^ n)⁻¹ ∈ h.F := fun n c hc =>
    (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.zpow_mem_zpowers g n)) c).mp hc
  intro e he
  refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨c₁, hc₁, n₁, rfl⟩ := hdec e he
  obtain ⟨c₂, hc₂, n₂, rfl⟩ := hdec x (hXE hx)
  have hcomm : c₁ * g ^ n₁ * (c₂ * g ^ n₂) * (c₁ * g ^ n₁)⁻¹ * (c₂ * g ^ n₂)⁻¹ ∈ h.F := by
    have e1 : c₁ * g ^ n₁ * (c₂ * g ^ n₂) * (c₁ * g ^ n₁)⁻¹ * (c₂ * g ^ n₂)⁻¹ =
        c₁ * (g ^ n₁ * c₂ * (g ^ n₁)⁻¹) * (g ^ n₂ * c₁⁻¹ * (g ^ n₂)⁻¹) * c₂⁻¹ := by
      have : g ^ n₁ * g ^ n₂ * (g ^ n₁)⁻¹ = g ^ n₂ := by
        rw [(Commute.zpow_zpow_self g n₁ n₂).eq, mul_inv_cancel_right]
      calc c₁ * g ^ n₁ * (c₂ * g ^ n₂) * (c₁ * g ^ n₁)⁻¹ * (c₂ * g ^ n₂)⁻¹ =
          c₁ * (g ^ n₁ * c₂ * (g ^ n₁)⁻¹) * (g ^ n₁ * g ^ n₂ * (g ^ n₁)⁻¹) * c₁⁻¹ *
            (g ^ n₂)⁻¹ * c₂⁻¹ := by group
        _ = _ := by rw [this]; group
    rw [e1]
    exact h.F.mul_mem (h.F.mul_mem (h.F.mul_mem hc₁ (hconjF n₁ c₂ hc₂))
      (hconjF n₂ _ (h.F.inv_mem hc₁))) (h.F.inv_mem hc₂)
  have : c₁ * g ^ n₁ * (c₂ * g ^ n₂) * (c₁ * g ^ n₁)⁻¹ =
      (c₁ * g ^ n₁ * (c₂ * g ^ n₂) * (c₁ * g ^ n₁)⁻¹ * (c₂ * g ^ n₂)⁻¹) * (c₂ * g ^ n₂) := by
    group
  rw [this]
  exact X.mul_mem (hFX hcomm) hx

theorem T_le_KX {X : Subgroup G} (hXE : X ≤ fr.E) : fr.T ≤ h.KX X := by
  refine fun t ht => ⟨ht.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (fr.E_le_CS (hXE hx)) t ht.1).symm

theorem div_eX_pos
    {X : Subgroup G} (hXE : X ≤ fr.E) : 0 < h.f / h.eX X := by
  have hdvd := (fr.eX_dvd_and_KX_iso hXE).1
  have hfpos := h.f_pos
  have hepos : 0 < h.eX X := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hdvd
    omega
  exact Nat.div_pos (Nat.le_of_dvd hfpos hdvd) hepos

theorem mod_eight_KX
    {X : Subgroup G} (hXE : X ≤ fr.E)
    (e : h.KX X ≃* PSL(2, GaloisField h.p (h.f / h.eX X))) :
    h.p ^ (h.f / h.eX X) % 8 = 3 ∨ h.p ^ (h.f / h.eX X) % 8 = 5 :=
  PSL2Sub.mod_eight e h.odd_p (fr.div_eX_pos hXE) fun _ _ hP => h.isMulCommutative_of_isPGroup hP

theorem exists_conj_of_cover
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {s : G}
    (hs : s ∈ (fr.S : Subgroup G)) (hs1 : s ≠ 1) :
    ∃ c ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (fr.E : Set G), c * s * c⁻¹ = h.J := by
  obtain ⟨n, hn, hns⟩ := fr.exists_conj_of_mem_S hidx hs hs1 fr.J_mem h.J_ne_one
  have hcov := fr.normalizer_S_eq hidx
  have hN : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (fr.E : Set G) ≤ Subgroup.normalizer (fr.CS : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hxS := Subgroup.mem_normalizer_iff.mp hx.1
    constructor
    · intro hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : x⁻¹ * w * x ∈ (fr.S : Subgroup G) := by
        have e0 : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
        refine (hxS (x⁻¹ * w * x)).mpr ?_
        rw [e0]
        exact hw
      have := Subgroup.mem_centralizer_iff.mp hz _ hw'
      calc w * (x * z * x⁻¹) = x * ((x⁻¹ * w * x) * z) * x⁻¹ := by group
        _ = x * (z * (x⁻¹ * w * x)) * x⁻¹ := by rw [this]
        _ = x * z * x⁻¹ * w := by group
    · intro hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : x * w * x⁻¹ ∈ (fr.S : Subgroup G) := (hxS w).mp hw
      have := Subgroup.mem_centralizer_iff.mp hz _ hw'
      have e1 : w * z = x⁻¹ * ((x * w * x⁻¹) * (x * z * x⁻¹)) * x := by group
      have e2 : z * w = x⁻¹ * ((x * z * x⁻¹) * (x * w * x⁻¹)) * x := by group
      rw [e1, e2, this]
  rw [hcov, sup_comm] at hn
  obtain ⟨z, hz, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hn
  refine ⟨c, hc, ?_⟩
  have hcs : c * s * c⁻¹ ∈ (fr.S : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hc.1 s).mp hs
  have hzc := Subgroup.mem_centralizer_iff.mp hz _ hcs
  rw [← hns]
  calc c * s * c⁻¹ = z * (c * s * c⁻¹) * z⁻¹ := by rw [← hzc, mul_inv_cancel_right]
    _ = z * c * s * (z * c)⁻¹ := by group

theorem S_le_commutator'
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {M : Subgroup G}
    (hM : Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓ Subgroup.centralizer (fr.E : Set G)
      ≤ Subgroup.normalizer (M : Set G)) {t : G} (htS : t ∈ (fr.S : Subgroup G)) (ht1 : t ≠ 1)
    (htM : t ∈ ⁅M, M⁆) : (fr.S : Subgroup G) ≤ ⁅M, M⁆ := by
  obtain ⟨c, hc, hct⟩ := fr.exists_conj_of_cover hidx htS ht1
  have hJ : h.J ∈ ⁅M, M⁆ := hct ▸ conj_mem_commutator_of_mem_normalizer (hM hc) htM
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]
    exact Subgroup.one_mem _
  obtain ⟨d, hd, hds⟩ := fr.exists_conj_of_cover hidx hs hs1
  have := conj_mem_commutator_of_mem_normalizer
    (Subgroup.inv_mem _ (hM hd)) hJ
  rwa [← hds, show d⁻¹ * (d * s * d⁻¹) * d⁻¹⁻¹ = s by group] at this

theorem exists_conj_in_JR
    {L K' : Subgroup G} {p' g : ℕ} [Fact p'.Prime] (hp' : p' ≠ 2)
    (hg : 0 < g) (hL : IsJRSubgroup L h.J K' p' g) (hSL : (fr.S : Subgroup G) ≤ L)
    (hST : Nat.card ((fr.S : Subgroup G) ⊓ K' : Subgroup G) = 4) {s : G}
    (hs : s ∈ (fr.S : Subgroup G)) (hs1 : s ≠ 1) :
    ∃ l ∈ L ⊓ Subgroup.normalizer ((fr.S : Subgroup G) : Set G), l * s * l⁻¹ = h.J := by
  have hK'L : K' ≤ L := hL.K_le.trans inf_le_left
  have hK'C : K' ≤ Subgroup.centralizer ({h.J} : Set G) := hL.K_le.trans inf_le_right
  have hKn : ∀ x ∈ L, x * h.J = h.J * x → ∀ k ∈ K', x * k * x⁻¹ ∈ K' := by
    intro x hxL hxJ k hk
    have hx : x ∈ Subgroup.zpowers h.J ⊔ K' := by
      rw [← hL.centralizer_eq]
      exact ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr hxJ⟩
    have hle : Subgroup.zpowers h.J ⊔ K' ≤ Subgroup.normalizer (K' : Set G) := by
      refine sup_le (le_trans ?_ (Subgroup.centralizer_le_normalizer (K' : Set G)))
        Subgroup.le_normalizer
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hK'C hk)
    exact (Subgroup.mem_normalizer_iff.mp (hle hx) k).mp hk
  obtain ⟨eK⟩ := hL.iso
  let hL' : Hyp L := h.ofSubgroup ⟨fr.S, hSL⟩ hL.J_mem hL.orderOf_J hK'L hK'C hKn p' g hp' hg eK
  have hcardT : Nat.card ↥(((fr.S.subtype hSL : Sylow 2 L) : Subgroup L) ⊓ hL'.K) = 4 := by
    have : ((fr.S.subtype hSL : Sylow 2 L) : Subgroup L) ⊓ hL'.K =
        ((fr.S : Subgroup G) ⊓ K').subgroupOf L := by
      rw [Sylow.coe_subtype, Hyp.ofSubgroup_K]
      exact Subgroup.ext fun _ => Iff.rfl
    rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hSL)).toEquiv, hST]
  let fr' : Frame hL' := ⟨fr.S.subtype hSL, hSL fr.J_mem |> fun _ => fr.J_mem, hcardT⟩
  have hidx' : ∀ N : Subgroup L, N.Normal → N.index ≠ 2 :=
    index_ne_two_subtype hL.index_ne_two
  have hs2 : orderOf (⟨s, hSL hs⟩ : L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact fr.mul_self_of_mem_S hs) hs1
  obtain ⟨n, hn, hns⟩ := (lemma_2_2 L hL' fr' hidx').2.1 ⟨s, hSL hs⟩ hs hL'.J fr.J_mem hs2
    hL'.orderOf_J
  refine ⟨n, ⟨n.2, JT.mem_normalizer_of_conj_mem fun y hy => ?_⟩, congrArg Subtype.val hns⟩
  have := (Subgroup.mem_normalizer_iff.mp hn ⟨y, hSL hy⟩).mp hy
  exact this

end Frame

end CFSG.Walter.W67
