module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutDatum
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieRel

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431

universe u

variable {G : Type u} [Group G] {K₀ T S : Subgroup G} {f : G} {N N' : Subgroup G} {z t : G}
  {V : Subgroup G}

theorem UnOutRel.toOut (R : UnOutRel K₀ T S f N N' z t V) :
    ∃ (g z' t' : ↥K₀), F431UnOut (T.subgroupOf K₀) (S.subgroupOf K₀) g (N.subgroupOf K₀)
      (N'.subgroupOf K₀) z' t' (V.subgroupOf K₀) := by
  have hT : T ≤ K₀ := R.sylow.1
  have hS : S ≤ K₀ := R.S_le.trans hT
  have hN : N ≤ K₀ := R.N_le
  have hN' : N' ≤ K₀ := R.N'_le
  have hV : V ≤ K₀ := R.V_le.trans hS
  have hz : z ∈ K₀ := hS R.z_mem
  have ht : t ∈ K₀ := hS R.t_mem
  have hf : f ∈ K₀ := hT R.f_mem
  have hspT : spTf T f ≤ K₀ := inf_le_left.trans hT
  refine ⟨⟨f, hf⟩, ⟨z, hz⟩, ⟨t, ht⟩, ?_⟩
  have hTf : spTf (T.subgroupOf K₀) (⟨f, hf⟩ : K₀) = (spTf T f).subgroupOf K₀ :=
    sub_inf_centralizer K₀ ⟨f, hf⟩
  have hTz : T.subgroupOf K₀ ⊓ Subgroup.centralizer ({(⟨z, hz⟩ : K₀)} : Set K₀) =
      (T ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf K₀ := sub_inf_centralizer K₀ ⟨z, hz⟩
  have hTt : T.subgroupOf K₀ ⊓ Subgroup.centralizer ({(⟨t, ht⟩ : K₀)} : Set K₀) =
      (T ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf K₀ := sub_inf_centralizer K₀ ⟨t, ht⟩
  have hCf : Subgroup.centralizer ({(⟨f, hf⟩ : K₀)} : Set K₀) ⊓ N.subgroupOf K₀ =
      (Subgroup.centralizer ({f} : Set G) ⊓ N).subgroupOf K₀ := sub_centralizer_inf K₀ ⟨f, hf⟩
  exact
  { sylow := by
      have := (sub_isSylowTwoOf_iff K₀ hT le_rfl).2 R.sylow
      rwa [Subgroup.subgroupOf_self] at this
    T_le := fun x hx => R.T_le hx
    T_le' := fun x hx => R.T_le' hx
    S_le := fun x hx => R.S_le hx
    S_norm := fun x hx => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have := Subgroup.mem_normalizer_iff.1 (R.S_norm hx) (y : G)
      exact this
    cyc := by
      obtain ⟨t₀, ht₀, e⟩ := R.cyc
      refine ⟨⟨t₀, hT ht₀⟩, ?_⟩
      apply Subgroup.map_injective K₀.subtype_injective
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, sub_map_subgroupOf K₀ hT,
        sub_map_subgroupOf K₀ hS]
      exact e
    z_mem := R.z_mem
    z_two := by
      rw [← Subgroup.orderOf_coe]
      exact R.z_two
    t_mem := R.t_mem
    t_two := by
      rw [← Subgroup.orderOf_coe]
      exact R.t_two
    zt_not_conj := by
      rw [isConj_iff]
      rintro ⟨c, hc⟩
      exact R.zt_not_conj c c.2 (congrArg Subtype.val hc)
    z_ZN := (sub_mem_centerOf_perfectCore K₀ hN ⟨z, hz⟩).2 R.z_ZN
    Z_sq := fun x hx =>
      Subtype.ext (R.Z_sq x ((sub_mem_centerOf_perfectCore K₀ hN x).1 hx))
    ZN_trans := fun x hx hx1 => by
      obtain ⟨m, hm, e⟩ := R.ZN_trans x ((sub_mem_centerOf_perfectCore K₀ hN x).1 hx)
        (fun h1 => hx1 (Subtype.ext h1))
      exact ⟨⟨m, hN hm⟩, hm, Subtype.ext e⟩
    center_T := fun w hw hc hw1 => by
      obtain ⟨m, hm, e⟩ := R.center_T w hw (fun y hy => congrArg Subtype.val
        (hc ⟨y, hT hy⟩ hy)) (fun h1 => hw1 (Subtype.ext h1))
      exact ⟨⟨m, hN hm⟩, hm, Subtype.ext e⟩
    fusion := fun x hx hx2 => by
      obtain ⟨i, hi, hch⟩ := R.fusion (x : G) hx (by rw [Subgroup.orderOf_coe]; exact hx2)
      have hiK : i ∈ K₀ := by
        rcases hi with rfl | rfl
        exacts [hz, ht]
      refine ⟨⟨i, hiK⟩, ?_, ?_⟩
      · rcases hi with rfl | rfl
        exacts [Or.inl rfl, Or.inr rfl]
      · refine sub_reflTransGen K₀ ?_ ?_ hch x.2 hiK
        · rintro a b ha hb ⟨haT, hbT, hm⟩
          refine ⟨haT, hbT, ?_⟩
          rcases hm with ⟨m, hm, e⟩ | ⟨m, hm, e⟩
          · exact Or.inl ⟨⟨m, hN hm⟩, hm, Subtype.ext e⟩
          · exact Or.inr ⟨⟨m, hN' hm⟩, hm, Subtype.ext e⟩
        · rintro a b ⟨haT, hbT, -⟩
          exact ⟨hT haT, hT hbT⟩
    V_le := fun x hx => R.V_le hx
    V_ab := fun a ha b hb => Subtype.ext (R.V_ab a ha b hb)
    V_sq := fun a ha => Subtype.ext (R.V_sq a ha)
    V_zt := ⟨R.V_zt.1, R.V_zt.2⟩
    V_eq := by
      ext x
      rw [Subgroup.mem_subgroupOf, sub_mem_centerOf_pCoreOf K₀ hN', R.V_eq]
    V_unique := fun E hE hab hsq hcard => by
      have hE1 : E.map K₀.subtype ≤ T := by
        rintro _ ⟨y, hy, rfl⟩
        exact hE hy
      have hcardE : Nat.card ↥(E.map K₀.subtype) = Nat.card ↥V := by
        rw [Subgroup.card_map_of_injective K₀.subtype_injective, hcard, sub_card K₀ hV]
      have := R.V_unique (E.map K₀.subtype) hE1 (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hab a ha b hb)) (by
        rintro _ ⟨a, ha, rfl⟩
        exact congrArg Subtype.val (hsq a ha)) hcardE
      apply Subgroup.map_injective K₀.subtype_injective
      rw [this, sub_map_subgroupOf K₀ hV]
    f_mem := R.f_mem
    f_not := R.f_not
    f_sq := Subtype.ext R.f_sq
    Tf_lt_z := by
      rw [hTf, hTz, sub_card K₀ hspT, sub_card K₀ (inf_le_left.trans hT)]
      exact R.Tf_lt_z
    Tf_lt_t := by
      rw [hTf, hTt, sub_card K₀ hspT, sub_card K₀ (inf_le_left.trans hT)]
      exact R.Tf_lt_t
    Sylow_Tf := by
      rw [hTf, hCf]
      have hle : spTf T f ≤ Subgroup.centralizer ({f} : Set G) ⊓ N :=
        fun x hx => ⟨hx.2, R.T_le hx.1⟩
      exact (sub_isSylowTwoOf_iff K₀ hle (inf_le_right.trans hN)).2 R.Sylow_Tf
    W_le := by
      rw [sub_spWf K₀ hT]
      exact fun x hx => R.W_le hx
    W_ne := by
      obtain ⟨x, hx, hxc, hx1⟩ := R.W_ne
      have hxK : x ∈ K₀ := hspT (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
      refine ⟨⟨x, hxK⟩, ?_, (sub_mem_centerOf_perfectCore K₀ hN ⟨x, hxK⟩).2 hxc,
        fun h1 => hx1 (congrArg Subtype.val h1)⟩
      rw [sub_spWf K₀ hT]
      exact hx
    W_cls := fun y hy hc => by
      rw [sub_spWf K₀ hT] at hy
      rw [isConj_iff] at hc
      obtain ⟨c, hc⟩ := hc
      exact (sub_mem_centerOf_perfectCore K₀ hN y).2
        (R.W_cls y hy ⟨c, c.2, congrArg Subtype.val hc⟩) }

end CFSG.Quasithin.H13.F431.Un
