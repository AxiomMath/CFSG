module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section NormAut

variable {Q : Type} [Group Q] (K : Subgroup Q)

@[expose] def normAut : ↥(Subgroup.normalizer (K : Set Q)) →* MulAut ↥K where
  toFun n :=
    { toFun := fun k => ⟨n * k * (n : Q)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 k).mp k.2⟩
      invFun := fun k => ⟨(n : Q)⁻¹ * k * n, by
        have h := (Subgroup.mem_normalizer_iff.mp (inv_mem n.2) k).mp k.2
        rwa [inv_inv] at h⟩
      left_inv := fun k => Subtype.ext (by simp only; group)
      right_inv := fun k => Subtype.ext (by simp only; group)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  map_one' := MulEquiv.ext fun k => Subtype.ext (by
    change ((1 : ↥(Subgroup.normalizer (K : Set Q))) : Q) * k * ((1 : ↥(Subgroup.normalizer
      (K : Set Q))) : Q)⁻¹ = k
    simp)
  map_mul' a b := MulEquiv.ext fun k => Subtype.ext (by
    change ((a * b : ↥(Subgroup.normalizer (K : Set Q))) : Q) * k *
      ((a * b : ↥(Subgroup.normalizer (K : Set Q))) : Q)⁻¹ = a * (b * k * (b : Q)⁻¹) * (a : Q)⁻¹
    simp only [Subgroup.coe_mul]
    group)

variable {K}

theorem normAut_of_mem (c : ↥K) :
    normAut K ⟨c, Subgroup.le_normalizer c.2⟩ = MulAut.conj c :=
  MulEquiv.ext fun _ => Subtype.ext rfl

end NormAut

structure AutConf (M : Type) [Group M] (ν : MulAut M) (Lb Pb : Subgroup (MulAut M)) : Prop where
  sq : ν ^ 2 = 1
  ne_one : ν ≠ 1
  sylow : ∃ S : Subgroup M, IsSylowTwoOf S ⊤ ∧ ∀ s ∈ S, ν s = s
  inv : ∀ x : M, Odd (orderOf x) → ν x = x⁻¹ → x ^ 3 = 1 ∨ x ^ 5 = 1
  comm : ∀ l ∈ Lb, l * ν = ν * l
  three : ∀ l ∈ Lb, Odd (orderOf l) → l ^ 3 = 1
  gen : oTwoUpper Lb = Lb
  ne_bot : Lb ≠ ⊥
  norm : ∀ c : M, ν c = c → ∀ l ∈ Lb, MulAut.conj c * l * (MulAut.conj c)⁻¹ ∈ Lb
  le : Pb ≤ Lb
  elem : IsElemAbelian 3 Pb

section Map

variable {M M' : Type} [Group M] [Group M']

theorem congr_conj (e : M ≃* M') (c : M) :
    MulAut.congr e (MulAut.conj c) = MulAut.conj (e c) :=
  MulEquiv.ext fun x => by
    change e (c * e.symm x * c⁻¹) = e c * x * (e c)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem isSylowTwoOf_map_equiv (e : M ≃* M') {S : Subgroup M} (h : IsSylowTwoOf S ⊤) :
    IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, h.2.1.map _, ?_⟩
  have h2 := h.2.2
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h2
  rw [show ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index
    from Subgroup.relIndex_top_right _, Subgroup.index_map_of_bijective e.bijective]
  exact h2

theorem AutConf.map (e : M ≃* M') {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)}
    (h : AutConf M ν Lb Pb) :
    AutConf M' (MulAut.congr e ν) (Lb.map (MulAut.congr e).toMonoidHom)
      (Pb.map (MulAut.congr e).toMonoidHom) where
  sq := by rw [← map_pow, h.sq, map_one]
  ne_one h1 := h.ne_one ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  sylow := by
    obtain ⟨S, hS, hSν⟩ := h.sylow
    refine ⟨S.map e.toMonoidHom, isSylowTwoOf_map_equiv e hS, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    change e (ν (e.symm (e s))) = e s
    rw [MulEquiv.symm_apply_apply, hSν s hs]
  inv x hx hinv := by
    have hx' : Odd (orderOf (e.symm x)) := by
      rwa [MulEquiv.orderOf_eq]
    have h1 : ν (e.symm x) = (e.symm x)⁻¹ := by
      have h2 : e (ν (e.symm x)) = x⁻¹ := hinv
      rw [← map_inv, ← h2, MulEquiv.symm_apply_apply]
    rcases h.inv _ hx' h1 with h3 | h5
    · left
      rw [← e.apply_symm_apply x, ← map_pow, h3, map_one]
    · right
      rw [← e.apply_symm_apply x, ← map_pow, h5, map_one]
  comm := by
    rintro _ ⟨l, hl, rfl⟩
    change MulAut.congr e l * MulAut.congr e ν = MulAut.congr e ν * MulAut.congr e l
    rw [← map_mul, ← map_mul, h.comm l hl]
  three := by
    rintro _ ⟨l, hl, rfl⟩ hodd
    have hodd' : Odd (orderOf l) := by
      rwa [orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective] at hodd
    change MulAut.congr e l ^ 3 = 1
    rw [← map_pow, h.three l hl hodd', map_one]
  gen := by
    refine le_antisymm (oTwoUpper_le _) (Subgroup.map_le_iff_le_comap.mpr ?_)
    calc Lb = oTwoUpper Lb := h.gen.symm
      _ ≤ _ := (Subgroup.closure_le _).mpr fun x hx => by
          show (MulAut.congr e).toMonoidHom x ∈ oTwoUpper (Lb.map (MulAut.congr e).toMonoidHom)
          refine Subgroup.subset_closure ⟨⟨x, hx.1, rfl⟩, ?_⟩
          rw [orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective]
          exact hx.2
  ne_bot hb := h.ne_bot (by
    rw [eq_bot_iff]
    intro l hl
    have h1 : MulAut.congr e l ∈ Lb.map (MulAut.congr e).toMonoidHom := ⟨l, hl, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr ((MulAut.congr e).injective (h1.trans (map_one _).symm)))
  norm c hc := by
    rintro _ ⟨l, hl, rfl⟩
    have hc' : ν (e.symm c) = e.symm c := by
      have h2 : e (ν (e.symm c)) = c := hc
      have h3 := congrArg e.symm h2
      rwa [MulEquiv.symm_apply_apply] at h3
    refine ⟨_, h.norm _ hc' l hl, ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm c) * l * (MulAut.conj (e.symm c))⁻¹) = _
    rw [map_mul, map_mul, map_inv, congr_conj, MulEquiv.apply_symm_apply]
    rfl
  le := Subgroup.map_mono h.le
  elem := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb]
      change MulAut.congr e x * MulAut.congr e y = MulAut.congr e y * MulAut.congr e x
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (h.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      change MulAut.congr e x ^ 3 = 1
      rw [← map_pow, h.elem.2 x hx, map_one]

end Map

section Conf

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

@[expose] def Conf12626.nu (h : Conf12626 K L P T v) : MulAut ↥K :=
  normAut K ⟨v, h.v_norm⟩

@[expose] def Conf12626.rhoL (h : Conf12626 K L P T v) : ↥L →* MulAut ↥K :=
  (normAut K).comp (Subgroup.inclusion h.L_norm)

@[expose] def Conf12626.rhoP (h : Conf12626 K L P T v) : ↥P →* MulAut ↥K :=
  (normAut K).comp (Subgroup.inclusion (h.P_le.trans h.L_norm))

theorem Conf12626.coe_nu_apply (h : Conf12626 K L P T v) (k : ↥K) :
    ((h.nu k : ↥K) : Q) = v * k * v⁻¹ :=
  rfl

theorem Conf12626.coe_rhoL_apply (h : Conf12626 K L P T v) (l : ↥L) (k : ↥K) :
    ((h.rhoL l k : ↥K) : Q) = l * k * (l : Q)⁻¹ :=
  rfl

theorem Conf12626.rhoL_pow_three [Finite Q] (h : Conf12626 K L P T v) {l : ↥L}
    (hl : Odd (orderOf (h.rhoL l))) : h.rhoL l ^ 3 = 1 := by
  obtain ⟨a, m, hm, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  have hpo : orderOf (l ^ 2 ^ a) = m := by
    rw [orderOf_pow' l (pow_ne_zero a two_ne_zero), ho, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
  have h3 : ((l : Q) ^ 2 ^ a) ^ 3 = 1 := by
    have := h.L_three ((l : Q) ^ 2 ^ a) (pow_mem l.2 _) (by
      rw [← Subgroup.coe_pow, Subgroup.orderOf_coe, hpo]
      exact hm)
    exact this
  have h1 : h.rhoL l ^ (2 ^ a * 3) = 1 := by
    rw [← map_pow, pow_mul]
    have : (l ^ 2 ^ a) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one]
      exact h3)
    rw [this, map_one]
  have hd := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (orderOf (h.rhoL l)) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hl)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hd)

theorem Conf12626.range_rhoL_le (h : Conf12626 K L P T v) :
    h.rhoL.range ≤ oTwoUpper h.rhoL.range := by
  rintro _ ⟨l, rfl⟩
  have hcl : Subgroup.closure {y | y ∈ L ∧ Odd (orderOf y)} ≤ L :=
    (Subgroup.closure_le L).mpr fun y hy => hy.1
  have hmem : ∀ x (hx : x ∈ Subgroup.closure {y | y ∈ L ∧ Odd (orderOf y)}),
      h.rhoL ⟨x, hcl hx⟩ ∈ oTwoUpper h.rhoL.range := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ⟨⟨_, rfl⟩, ?_⟩
      have hodd : Odd (orderOf (⟨y, hy.1⟩ : ↥L)) := by
        rw [← Subgroup.orderOf_coe]
        exact hy.2
      exact Odd.of_dvd_nat hodd (orderOf_map_dvd _ _)
    | one => exact (show h.rhoL ⟨1, _⟩ = 1 from map_one h.rhoL) ▸ one_mem _
    | mul x y hx hy ihx ihy =>
      have := mul_mem ihx ihy
      rwa [← map_mul] at this
    | inv x hx ihx =>
      have := inv_mem ihx
      rwa [← map_inv] at this
  have hl : (l : Q) ∈ Subgroup.closure {y | y ∈ L ∧ Odd (orderOf y)} := by
    have h1 : (l : Q) ∈ oTwoUpper L := by rw [h.L_gen]; exact l.2
    exact h1
  exact hmem l hl

theorem Conf12626.exists_sylow [Finite Q] (h : Conf12626 K L P T v) :
    ∃ S : Subgroup ↥K, IsSylowTwoOf S ⊤ ∧ ∀ s ∈ S, h.nu s = s := by
  have hS := RankOneRecog.isSylowTwoOf_inf_of_subnormal h.sylow le_top
    (h.comp.2.subgroupOf (K := ⊤))
  refine ⟨(T ⊓ K).subgroupOf K, ⟨le_top, ?_, ?_⟩, fun s hs => ?_⟩
  · exact hS.2.1.comap_of_injective K.subtype K.subtype_injective
  · rw [show (((T ⊓ K).subgroupOf K).subgroupOf ⊤).index = ((T ⊓ K).subgroupOf K).index from
      Subgroup.relIndex_top_right _]
    exact hS.2.2
  · apply Subtype.ext
    rw [Conf12626.coe_nu_apply, h.v_central _ (Subgroup.mem_subgroupOf.mp hs).1,
      mul_inv_cancel_right]

theorem Conf12626.autConf [Finite Q] (h : Conf12626 K L P T v) :
    AutConf ↥K h.nu h.rhoL.range h.rhoP.range where
  sq := by
    rw [Conf12626.nu, ← map_pow]
    convert map_one (normAut K)
    exact Subtype.ext h.v_sq
  ne_one := by
    intro h1
    obtain ⟨k, hk, hvk⟩ := h.v_nc
    apply hvk
    have := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : Q)) h1
    simp only [Conf12626.coe_nu_apply, MulAut.one_apply] at this
    calc v * k = v * k * v⁻¹ * v := by group
      _ = k * v := by rw [this]
  sylow := h.exists_sylow
  inv x hx hinv := by
    have hx' : Odd (orderOf (x : Q)) := by rw [Subgroup.orderOf_coe]; exact hx
    have h1 : v * x * v⁻¹ = (x : Q)⁻¹ := by
      rw [← h.coe_nu_apply, hinv, Subgroup.coe_inv]
    rcases h.inv x hx' h1 with h3 | h5
    · exact Or.inl (Subtype.ext (by rw [Subgroup.coe_pow, h3, Subgroup.coe_one]))
    · exact Or.inr (Subtype.ext (by rw [Subgroup.coe_pow, h5, Subgroup.coe_one]))
  comm := by
    rintro _ ⟨l, rfl⟩
    rw [Conf12626.rhoL, Conf12626.nu, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.L_cent l l.2).symm
  three := by
    rintro _ ⟨l, rfl⟩ hl
    exact h.rhoL_pow_three hl
  gen := le_antisymm (oTwoUpper_le _) h.range_rhoL_le
  ne_bot := by
    obtain ⟨l, hl, k, hk, hlk⟩ := h.L_nc
    intro hb
    have h1 : h.rhoL ⟨l, hl⟩ ∈ h.rhoL.range := ⟨_, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    apply hlk
    have := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : Q)) h1
    simp only [Conf12626.coe_rhoL_apply, MulAut.one_apply] at this
    calc l * k = l * k * l⁻¹ * l := by group
      _ = k * l := by rw [this]
  norm := by
    rintro c hc _ ⟨l, rfl⟩
    have hcv : (c : Q) ∈ Subgroup.centralizer ({v} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg Subtype.val hc
      rw [h.coe_nu_apply] at this
      calc (c : Q) * v = v * c * v⁻¹ * v := by rw [this]
        _ = v * c := by group
    have hcl : (c : Q) * l * (c : Q)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (h.L_star hcv) l).mp l.2
    refine ⟨⟨_, hcl⟩, ?_⟩
    rw [← normAut_of_mem, ← map_inv, Conf12626.rhoL]
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul]
    congr 1
  le := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨p, h.P_le p.2⟩, rfl⟩
  elem := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul]
      congr 1
      exact h.P_elem.1.is_comm.comm x y
    · rintro _ ⟨p, rfl⟩
      rw [← map_pow]
      have : p ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, h.P_elem.2 p p.2, Subgroup.coe_one])
      rw [this, map_one]

theorem Conf12626.mem_of_centralizes (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    {E : Subgroup Q} (hEK : E ≤ K) (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {p : Q}
    (hp : p ∈ P) (hpc : ∀ k ∈ K, p * k = k * p) : p ∈ K := by
  have := hQ.finite
  by_contra hpK
  have hp3 : p ^ 3 = 1 := h.P_elem.2 p hp
  have hp1 : p ≠ 1 := fun h1 => hpK (h1 ▸ one_mem K)
  have hop : orderOf p = 3 := orderOf_eq_prime hp3 hp1
  have hcomm : ∀ (a : ↥E) (b : ↥(Subgroup.zpowers p)),
      Commute (E.subtype a) ((Subgroup.zpowers p).subtype b) := by
    intro a b
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : Q) (b : Q)
    rw [← hn]
    exact (Commute.zpow_right (hpc a (hEK a.2)).symm n)
  let f : ↥E × ↥(Subgroup.zpowers p) →* Q :=
    MonoidHom.noncommCoprod E.subtype (Subgroup.zpowers p).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : Q) * b = 1 := hab
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    have hbE : (b : Q) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hab']
      exact inv_mem a.2
    have hb1 : (b : Q) = 1 := by
      by_contra hb1
      apply hpK
      apply hEK
      have h3n : ¬ (3 : ℤ) ∣ n := by
        intro hd
        obtain ⟨m, rfl⟩ := hd
        apply hb1
        rw [← hn, zpow_mul, show (p ^ (3 : ℤ)) = p ^ 3 from zpow_natCast p 3, hp3, one_zpow]
      have hsq : p = (p ^ n) ^ n := by
        rw [← zpow_mul, ← zpow_mod_orderOf, hop]
        conv_lhs => rw [← zpow_one p]
        congr 1
        push_cast
        have h1 : n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases h1 with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
      rw [hsq]
      exact zpow_mem (hn ▸ hbE) n
    have ha1 : (a : Q) = 1 := by rw [hb1, mul_one] at hab'; exact hab'
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hcard : Nat.card (↥E × ↥(Subgroup.zpowers p)) = 3 ^ 3 := by
    rw [Nat.card_prod, Nat.card_zpowers, hop, hE9]
    norm_num
  have hA := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
    (A := ↥E × ↥(Subgroup.zpowers p))
    (fun a b => Prod.ext (hE.1.is_comm.comm a.1 b.1)
      (Subtype.ext (by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2.2
        change (a.2 : Q) * b.2 = b.2 * a.2
        rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm])))
    (fun a => Prod.ext (Subtype.ext (by
        change ((a.1 : Q)) ^ 3 = 1
        exact hE.2 _ a.1.2))
      (Subtype.ext (by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        change ((a.2 : Q)) ^ 3 = 1
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp3, one_zpow])))
    hcard f hf (H := ⊤) le_top
  have h2 := hQ.sqt 3 Nat.prime_three (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

theorem Conf12626.card_rhoP_range [Finite Q] (h : Conf12626 K L P T v)
    (hP : ∀ p ∈ P, (∀ k ∈ K, p * k = k * p) → p = 1) : Nat.card h.rhoP.range = 9 := by
  have hinj : Function.Injective h.rhoP := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hP p p.2 fun k hk => ?_
    have := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : Q)) hp
    simp only [MulAut.one_apply] at this
    change (p : Q) * k * (p : Q)⁻¹ = k at this
    calc (p : Q) * k = p * k * (p : Q)⁻¹ * p := by group
      _ = k * p := by rw [this]
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, h.P_card]

theorem Conf12626.card_rhoP_range_eq_nine (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) {E : Subgroup ↥K} (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hZ : ∀ z ∈ Subgroup.center ↥K, z ^ 3 = 1 → z = 1) : Nat.card h.rhoP.range = 9 := by
  have := hQ.finite
  have hE' : IsElemAbelian 3 (E.map K.subtype) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
      exact congrArg (fun z : ↥E => K.subtype z) (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  have hE9' : Nat.card (E.map K.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hE9]
  refine h.card_rhoP_range fun p hp hpc => ?_
  have hpK := h.mem_of_centralizes hQ (Subgroup.map_subtype_le E) hE' hE9' hp hpc
  have hz : (⟨p, hpK⟩ : ↥K) ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hpc k k.2).symm
  have h1 := hZ _ hz (Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h.P_elem.2 p hp))
  exact congrArg Subtype.val h1

theorem Conf12626.mem_center_of_centralizes (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) {E : Subgroup Q} (hEK : E ≤ K) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {p : Q} (hp : p ∈ P) (hpc : ∀ k ∈ K, p * k = k * p) :
    ∃ hpK : p ∈ K, (⟨p, hpK⟩ : ↥K) ∈ Subgroup.center ↥K :=
  ⟨h.mem_of_centralizes hQ hEK hE hE9 hp hpc,
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hpc k k.2).symm⟩

end Conf

end CFSG.Quasithin.H13.S126C
