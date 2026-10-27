module

public import CFSG.Quasithin.H13.A6Realize
public import CFSG.Quasithin.H13.L32NModule
public import CFSG.Quasithin.H13.A5Inputs

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

theorem allOnes_not_mem_coreMod : G6.allOnes 5 ∉ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  decide

theorem allOnes5_sq : G6.allOnes 5 ^ 2 = 1 := by decide

theorem allOnes5_ne_one : G6.allOnes 5 ≠ 1 := by decide

theorem conjAct_coe {G : Type} [Group G] (V : Subgroup G) (g : ↥(Subgroup.normalizer (V : Set G)))
    (v : ↥V) : ((conjAct V g v : ↥V) : G) = g * v * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g v

theorem mem_zpowers_allOnes5 {x : G6.PermMod 5} :
    x ∈ Subgroup.zpowers (G6.allOnes 5) → x = 1 ∨ x = G6.allOnes 5 := by
  rintro ⟨k, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf (G6.allOnes 5) = 2 := orderOf_eq_prime allOnes5_sq allOnes5_ne_one
  show G6.allOnes 5 ^ k = 1 ∨ G6.allOnes 5 ^ k = G6.allOnes 5
  rw [← zpow_mod_orderOf, h2]
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h | h <;> rw [h]
  · left; exact zpow_zero _
  · right; exact zpow_one _

@[expose] def nat5Hom : ↥(FFModel.altDn 5).sec →* W5 where
  toFun x := Multiplicative.ofAdd
    ⟨Multiplicative.toAdd (show G6.PermMod 5 from x.1), mem_Ev.2 (G6.mem_coreMod.1 x.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem nat5Hom_surjective : Function.Surjective nat5Hom := fun w =>
  ⟨⟨(show (FFModel.altDn 5).Amb from
      Multiplicative.ofAdd ((Multiplicative.toAdd w : ↥Ev) : Fin 5 → ZMod 2)),
    G6.mem_coreMod.2 (mem_Ev.1 (Multiplicative.toAdd w).2)⟩, rfl⟩

theorem ker_nat5Hom :
    (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = nat5Hom.ker := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hx' : (show G6.PermMod 5 from x.1) ∈ Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 := hx
    rcases mem_zpowers_allOnes5 hx'.1 with h | h
    · have : x = 1 := Subtype.ext h
      rw [this, map_one]
    · exact absurd (h ▸ x.2) allOnes_not_mem_coreMod
  · intro hx
    have h1 : x = 1 := by
      apply Subtype.ext
      have := congrArg (fun w : W5 => ((Multiplicative.toAdd w : ↥Ev) : Fin 5 → ZMod 2)) hx
      exact this
    rw [h1]
    exact Subgroup.one_mem _

@[expose] noncomputable def modW5Equiv : (FFModel.altDn 5).Mod ≃* W5 :=
  (QuotientGroup.quotientMulEquivOfEq ker_nat5Hom).trans
    (QuotientGroup.quotientKerEquivOfSurjective nat5Hom nat5Hom_surjective)

theorem modW5Equiv_mk (m : ↥(FFModel.altDn 5).sec) :
    modW5Equiv (QuotientGroup.mk m) = nat5Hom m := by
  rw [modW5Equiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem nat5Hom_act (σ : ↥(alternatingGroup (Fin 5))) (m : ↥(FFModel.altDn 5).sec)
    (hm : (FFModel.altDn 5).act σ (m : (FFModel.altDn 5).Amb) ∈ (FFModel.altDn 5).sec) :
    nat5Hom ⟨(FFModel.altDn 5).act σ (m : (FFModel.altDn 5).Amb), hm⟩ =
      pact (σ : Equiv.Perm (Fin 5)) (nat5Hom m) := rfl

variable {G : Type} [Group G]

theorem autOnHom_eq_one_iff {L V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (l : ↥L) : A6.autOnHom hL l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 := DFunLike.congr_fun (congrArg Subtype.val h) ⟨v, hv⟩
    rw [A6.autOnHom_apply] at h1
    have h2 := congrArg Subtype.val h1
    have h3 : (l : G) * v * (l : G)⁻¹ = v := by
      rw [← conjAct_coe V ⟨l, hL l.2⟩ ⟨v, hv⟩]
      simpa using h2
    calc v * (l : G) = (l : G) * v * (l : G)⁻¹ * l := by rw [h3]
      _ = (l : G) * v := by group
  · intro h
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    rw [A6.autOnHom_apply]
    apply Subtype.ext
    rw [conjAct_coe V ⟨l, hL l.2⟩ v]
    show (l : G) * v * (l : G)⁻¹ = ((1 : MulAut ↥V) v : G)
    rw [MulAut.one_apply, ← h v v.2]
    group

theorem exists_rawData5_of_nat {L V : Subgroup G} [IsMulCommutative ↥V]
    (hL : L ≤ Subgroup.normalizer (V : Set G))
    (h : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 5) :
    Nonempty (RawData5 L (Subgroup.centralizer (V : Set G)) V) := by
  obtain ⟨π, hπ⟩ := h
  have hinj := hπ.injective_of_faithful (A6.altDn_faithful (by norm_num))
  let e : ↥(alternatingGroup (Fin 5)) ≃* ↥(autOn L V) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_modEquiv hπ
  refine ⟨{ hnorm := hL
            θ := e.symm.toMonoidHom.comp (A6.autOnHom hL)
            ψ := E.trans modW5Equiv
            surj := e.symm.surjective.comp (A6.autOnHom_surjective hL)
            ker_eq := ?_
            equiv := fun l v => ?_ }⟩
  · ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← autOnHom_eq_one_iff hL l]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h1 => by simpa using congrArg e h1, fun h1 => by rw [h1, map_one]⟩
  · have he : ((π (e.symm (A6.autOnHom hL l)) : ↥(autOn L V)) : MulAut ↥V) =
        conjAct V ⟨l, hL l.2⟩ := by
      have : π (e.symm (A6.autOnHom hL l)) = A6.autOnHom hL l := e.apply_symm_apply _
      rw [this, A6.autOnHom_apply]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (E v)
    have hact : (FFModel.altDn 5).act (e.symm (A6.autOnHom hL l)) m.1 ∈ (FFModel.altDn 5).sec :=
      G6.permAct_mem_coreMod _ m.2
    have h1 := hE (e.symm (A6.autOnHom hL l)) v m hact hm.symm
    rw [he] at h1
    show modW5Equiv (E (conjAct V ⟨l, hL l.2⟩ v)) =
      pact ((e.symm (A6.autOnHom hL l) : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
        (modW5Equiv (E v))
    rw [h1, ← hm, modW5Equiv_mk, modW5Equiv_mk]
    exact nat5Hom_act _ m hact

theorem not_nine_dvd_card_autOn [Finite G] {K V : Subgroup G}
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) : ¬ 9 ∣ Nat.card (autOn K V) := by
  intro h9
  rw [card_autOn_eq_relIndex hKV] at h9
  have hdvd := Subgroup.relIndex_dvd_card (K ⊓ Subgroup.centralizer (V : Set G)) K
  have hK' : Nat.card ↥K = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) * Nat.card (CFSG.pCore 2 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨e⟩ := hK
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [Nat.card_congr e.toEquiv, h60] at hK'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  rw [hk] at hK'
  have h9K : 9 ∣ 60 * 2 ^ k := hK' ▸ h9.trans hdvd
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have := hcop.dvd_of_dvd_mul_right h9K
  norm_num at this

theorem modules13_3_2_of_A5 [Finite G] {K V : Subgroup G} [IsMulCommutative ↥V]
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hne : ¬ K ≤ Subgroup.centralizer (V : Set G))
    (h : Modules13_3_2 K V) :
    AlternatingNatural (V := ↥V) (autOn K V) ⊤ ⊥ 5 ∧
      V ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have hA := autOn_ne_bot_of_not_le_centralizer hKV hne
  have h9 := not_nine_dvd_card_autOn hK hKV
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  obtain ⟨eK⟩ := hK
  rcases h with ha | ⟨⟨π, hπ, -⟩, -⟩ | ⟨-, -, ⟨π, hπ, -⟩⟩ | ⟨hd, -, -⟩ | ⟨he, -, -⟩
  · exact ha
  · rw [card_autOn_of_alt (by norm_num) hA π hπ] at h9
    exact absurd (by decide) h9
  · rw [card_autOn_of_alt (by norm_num) hA π hπ] at h9
    exact absurd (by decide) h9
  · obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hd
    have h1 := Nat.card_congr (eK.symm.toEquiv.trans e.toEquiv)
    rw [h60, HSType.card_SL_three_two] at h1
    norm_num at h1
  · have h1 := card_of_lieModel_PSU_three_three he
    rw [Nat.card_congr eK.toEquiv, h60] at h1
    norm_num at h1

theorem stmt13_3_2_three_A5_of (h1332 : Stmt13_3_2) : Stmt13_3_2_three_A5 := by
  intro G _ _ T L h K hK hK5 V hV
  obtain ⟨-, -, -, hc, hmod⟩ := (h1332 G T L h K hK).2.2.1.2 V hV
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hne : ¬ K ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    have h1 : ⁅V, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
    exact hV.2.1 (hV.2.2.2.1.symm.trans h1)
  obtain ⟨hnat, -⟩ := modules13_3_2_of_A5 ((quasithinO2QuotientIso_iff K _).1 hK5) hKV hne hmod
  exact exists_rawData5_of_nat hKV hnat

end CFSG.Quasithin.H13.A5
