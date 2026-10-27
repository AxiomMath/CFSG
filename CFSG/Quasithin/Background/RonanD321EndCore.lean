module

public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Background.SmithD321Q
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.RonanD321.EndCore

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391
  CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise Matrix

section Coord

variable {W : Type*} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)} {π : ↥Γ →* ↥H}

theorem exists_coord_nat (hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    ∃ E : W ≃* Multiplicative (ι → K), ∀ (γ : ↥Γ) (w : W),
      Multiplicative.toAdd (E (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (E w) := by
  set D := FFModel.nat Γ
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  let q : (↥D.sec ⧸ D.ker.subgroupOf D.sec) →* D.Amb :=
    QuotientGroup.lift _ D.sec.subtype (by
      intro m hm
      rw [Subgroup.mem_subgroupOf] at hm
      exact Subgroup.mem_bot.mp hm)
  have hq : ∀ m : ↥D.sec, q (QuotientGroup.mk m) = (m : D.Amb) := fun m => rfl
  let e0 : W →* D.Amb := q.comp (β.comp Subgroup.topEquiv.symm.toMonoidHom)
  have he0 : ∀ w, e0 w = q (β ⟨w, trivial⟩) := fun w => rfl
  have hinj : Function.Injective e0 := by
    rw [injective_iff_map_eq_one]
    intro w hw
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
    rw [he0, ← hm, hq] at hw
    have h1 : β ⟨w, trivial⟩ = 1 := by
      rw [← hm, show m = 1 from Subtype.ext hw]
      rfl
    exact Subgroup.mem_bot.mp ((hβk ⟨w, trivial⟩).mp h1)
  have hsurj : Function.Surjective e0 := by
    intro y
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y, trivial⟩)
    refine ⟨u, ?_⟩
    rw [he0, show (⟨(u : W), trivial⟩ : ↥(⊤ : Subgroup W)) = u from rfl, hu]
    rfl
  refine ⟨MulEquiv.ofBijective e0 ⟨hinj, hsurj⟩, fun γ w => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
  have h1 : β ⟨((π γ : ↥H) : MulAut W) w, trivial⟩ =
      QuotientGroup.mk ⟨D.act γ (m : D.Amb), trivial⟩ :=
    hβe γ ⟨w, trivial⟩ m trivial trivial hm.symm
  show Multiplicative.toAdd (e0 _) =
    ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e0 w)
  rw [he0, he0, h1, ← hm, hq, hq]
  rfl

end Coord

section NatCoord

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]
  {K : Type} [Field K]

@[expose] def IsNatCoord (Λ : Subgroup Γ) (S : Subgroup Q) (σ : ↥(StatedSL 2 K) →* ↥Λ)
    (E : ↥S ≃* Multiplicative (Fin 2 → K)) : Prop :=
  ∀ (γ : ↥(StatedSL 2 K)) (s s' : ↥S), ((σ γ : ↥Λ) : Γ) • (s : Q) = (s' : Q) →
    Multiplicative.toAdd (E s') =
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd (E s)

variable {Λ : Subgroup Γ} {S : Subgroup Q} {σ : ↥(StatedSL 2 K) →* ↥Λ}
  {E : ↥S ≃* Multiplicative (Fin 2 → K)}

theorem toAdd_eq_zero_iff (E : ↥S ≃* Multiplicative (Fin 2 → K)) {s : ↥S} :
    Multiplicative.toAdd (E s) = 0 ↔ s = 1 := by
  constructor
  · intro h
    have h1 : E s = 1 := by rw [← ofAdd_toAdd (E s), h, ofAdd_zero]
    exact E.injective (h1.trans (map_one E).symm)
  · rintro rfl
    rw [map_one, toAdd_one]

theorem card_eq_of_coord [Finite K] (E : ↥S ≃* Multiplicative (Fin 2 → K)) :
    Nat.card ↥S = Nat.card K ^ 2 := by
  rw [Nat.card_congr E.toEquiv, Nat.card_congr (Multiplicative.toAdd : _ ≃ (Fin 2 → K)),
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]

theorem IsNatCoord.isIrr (hS : XMod.IsInv ↥Λ S) (hE : IsNatCoord Λ S σ E) :
    XMod.IsIrr ↥Λ S := by
  refine ⟨hS, bot_lt_iff_ne_bot.2 fun h => ?_, fun J hJ _ hJS => ?_⟩
  · have h1 : E.symm (Multiplicative.ofAdd (Pi.single 0 1)) = 1 :=
      Subtype.ext ((Subgroup.eq_bot_iff_forall S).1 h _ (E.symm _).2)
    have h2 := (toAdd_eq_zero_iff E).2 h1
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h2
    have h3 := congrFun h2 0
    simp at h3
  · rcases Subgroup.bot_or_exists_ne_one J with hJ0 | ⟨j, hjJ, hj1⟩
    · exact Or.inl hJ0
    right
    let A : AddSubgroup (Fin 2 → K) :=
      { carrier := {v | ∃ s : ↥S, (s : Q) ∈ J ∧ Multiplicative.toAdd (E s) = v}
        zero_mem' := ⟨1, J.one_mem, by rw [map_one, toAdd_one]⟩
        add_mem' := by
          rintro _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
          exact ⟨s * s', J.mul_mem hs hs', by rw [map_mul, toAdd_mul]⟩
        neg_mem' := by
          rintro _ ⟨s, hs, rfl⟩
          exact ⟨s⁻¹, J.inv_mem hs, by rw [map_inv, toAdd_inv]⟩ }
    have hA : ∀ g : ↥(StatedSL 2 K), ∀ v ∈ A,
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ A := by
      rintro g _ ⟨s, hs, rfl⟩
      have hs' : ((σ g : ↥Λ) : Γ) • (s : Q) ∈ S := hS (σ g) _ s.2
      exact ⟨⟨_, hs'⟩, hJ (σ g) _ hs, (hE g s ⟨_, hs'⟩ rfl)⟩
    have hjA : Multiplicative.toAdd (E ⟨j, hJS hjJ⟩) ∈ A := ⟨_, hjJ, rfl⟩
    have hne : Multiplicative.toAdd (E ⟨j, hJS hjJ⟩) ≠ 0 := fun h0 =>
      hj1 (congrArg Subtype.val ((toAdd_eq_zero_iff E).1 h0))
    have htop := eq_top_of_slMulVec_mem le_rfl hA hjA hne
    refine le_antisymm hJS fun s hs => ?_
    have hmem : Multiplicative.toAdd (E ⟨s, hs⟩) ∈ A := htop ▸ AddSubgroup.mem_top _
    obtain ⟨s', hs'J, hs'⟩ := hmem
    have he : s' = ⟨s, hs⟩ := E.injective (Multiplicative.toAdd.injective hs')
    rw [he] at hs'J
    exact hs'J

theorem IsNatCoord.iso {S' : Subgroup Q} {E' : ↥S' ≃* Multiplicative (Fin 2 → K)}
    (hσ : Function.Surjective σ) (hS' : XMod.IsInv ↥Λ S') (hE : IsNatCoord Λ S σ E)
    (hE' : IsNatCoord Λ S' σ E') : XMod.Iso ↥Λ S S' := by
  refine ⟨E.trans E'.symm, fun a l l' hll' => ?_⟩
  obtain ⟨γ, rfl⟩ := hσ a
  have hx : ((σ γ : ↥Λ) : Γ) • (((E.trans E'.symm) l : ↥S') : Q) ∈ S' :=
    hS' (σ γ) _ (E.trans E'.symm l).2
  have h1 := hE' γ ((E.trans E'.symm) l) ⟨_, hx⟩ rfl
  have h2 := hE γ l l' hll'
  have h3 : (⟨_, hx⟩ : ↥S') = (E.trans E'.symm) l' := by
    apply E'.injective
    apply Multiplicative.toAdd.injective
    rw [h1]
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact h2.symm
  exact congrArg Subtype.val h3

theorem IsNatCoord.eq_one_of_fixed (hE : IsNatCoord Λ S σ E) {s : ↥S}
    (hs : ∀ l : ↥Λ, (l : Γ) • (s : Q) = s) : s = 1 := by
  have key : ∀ {i j : Fin 2} (hij : i ≠ j), Multiplicative.toAdd (E s) j = 0 := by
    intro i j hij
    have h1 := hE (slElTrans hij 1) s s (hs _)
    rw [mulVec_slElTrans, one_mul, left_eq_add] at h1
    have h2 := congrFun h1 i
    simpa using h2
  refine (toAdd_eq_zero_iff E).1 (funext fun j => ?_)
  fin_cases j
  · exact key (i := 1) (by decide)
  · exact key (i := 0) (by decide)

theorem IsNatCoord.card_eqv (hσ : Function.Surjective σ) (hS : XMod.IsInv ↥Λ S)
    (hE : IsNatCoord Λ S σ E) :
    Nat.card {θ : ↥S →* ↥S // IsEqv Λ (S.subtype.comp θ)} = Nat.card K := by
  classical
  let fth : (↥S →* ↥S) → (Fin 2 → K) →+ (Fin 2 → K) := fun θ =>
    { toFun := fun v => Multiplicative.toAdd (E (θ (E.symm (Multiplicative.ofAdd v))))
      map_zero' := by simp
      map_add' := fun x y => by rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul] }
  have hfth : ∀ (θ : ↥S →* ↥S) (u : ↥S),
      fth θ (Multiplicative.toAdd (E u)) = Multiplicative.toAdd (E (θ u)) := by
    intro θ u
    simp [fth]
  have hsurjE : ∀ v : Fin 2 → K, ∃ u, Multiplicative.toAdd (E u) = v :=
    fun v => ⟨E.symm (Multiplicative.ofAdd v), by simp⟩
  have hγ : ∀ (θ : {θ : ↥S →* ↥S // IsEqv Λ (S.subtype.comp θ)}) (γ : ↥(StatedSL 2 K))
      (v : Fin 2 → K), fth θ.1 (((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ fth θ.1 v := by
    intro θ γ v
    obtain ⟨u, rfl⟩ := hsurjE v
    have hu' : ((σ γ : ↥Λ) : Γ) • (u : Q) ∈ S := hS (σ γ) _ u.2
    have h1 := hE γ u ⟨_, hu'⟩ rfl
    have hv' : ((σ γ : ↥Λ) : Γ) • ((θ.1 u : ↥S) : Q) ∈ S := hS (σ γ) _ (θ.1 u).2
    have h2 : θ.1 ⟨_, hu'⟩ = ⟨_, hv'⟩ := Subtype.ext (θ.2 (σ γ) u ⟨_, hu'⟩ rfl)
    have h3 := hE γ (θ.1 u) ⟨_, hv'⟩ rfl
    rw [← h1, hfth, hfth, h2, h3]
  let Φ : {θ : ↥S →* ↥S // IsEqv Λ (S.subtype.comp θ)} → K := fun θ =>
    fth θ.1 (Pi.single 0 1) 0
  have hΦ : Function.Injective Φ := by
    intro θ θ' h
    obtain ⟨c, hc⟩ := exists_smul_of_comm_sl le_rfl (fth θ.1) (hγ θ)
    obtain ⟨c', hc'⟩ := exists_smul_of_comm_sl le_rfl (fth θ'.1) (hγ θ')
    have hcc : c = c' := by
      have e1 : Φ θ = c := by simp [Φ, hc]
      have e2 : Φ θ' = c' := by simp [Φ, hc']
      rw [← e1, ← e2, h]
    apply Subtype.ext
    refine MonoidHom.ext fun u => E.injective (Multiplicative.toAdd.injective ?_)
    rw [← hfth, ← hfth, hc, hc', hcc]
  have hΦs : Function.Surjective Φ := by
    intro c
    let mc : Multiplicative (Fin 2 → K) →* Multiplicative (Fin 2 → K) :=
      AddMonoidHom.toMultiplicative
        { toFun := fun v => c • v, map_zero' := smul_zero c, map_add' := smul_add c }
    let θc : ↥S →* ↥S := E.symm.toMonoidHom.comp (mc.comp E.toMonoidHom)
    have hθc : ∀ u, Multiplicative.toAdd (E (θc u)) = c • Multiplicative.toAdd (E u) := by
      intro u
      simp [θc, mc]
    refine ⟨⟨θc, fun l v w hvw => ?_⟩, ?_⟩
    · obtain ⟨γ, rfl⟩ := hσ l
      have hx : ((σ γ : ↥Λ) : Γ) • ((θc v : ↥S) : Q) ∈ S := hS _ _ (θc v).2
      have h1 := hE γ (θc v) ⟨_, hx⟩ rfl
      have h2 := hE γ v w hvw
      have h3 : θc w = ⟨_, hx⟩ := by
        apply E.injective
        apply Multiplicative.toAdd.injective
        rw [h1, hθc, hθc, h2, Matrix.mulVec_smul]
      show ((θc w : ↥S) : Q) = _
      rw [h3]
      rfl
    · show fth θc (Pi.single 0 1) 0 = c
      have h1 := hfth θc (E.symm (Multiplicative.ofAdd (Pi.single 0 1)))
      rw [hθc, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h1
      rw [h1]
      simp
  exact Nat.card_eq_of_bijective Φ ⟨hΦ, hΦs⟩

end NatCoord

section Unpack

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem two_le_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) : 2 ≤ n := by
  obtain ⟨⟨-, hn1, -, hne, -⟩, -⟩ := h
  by_contra hlt
  have h1 : n = 1 := by omega
  subst h1
  exact hne rfl

theorem exists_natCoord (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L) :
    letI := qAct hB.hD.hyp.Mp_normal
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (S : Fin 2 → Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))
      (σ : ↥(StatedSL 2 K) →* ↥(L.subgroupOf M))
      (E : ∀ i, ↥(S i) ≃* Multiplicative (Fin 2 → K)),
      IsPSL 2 2 n ↥L ∧ Nat.card K = 2 ^ n ∧ Function.Bijective σ ∧
      (∀ i, XMod.IsInv ↥(L.subgroupOf M) (S i)) ∧
      (∀ i, IsNatCoord (L.subgroupOf M) (S i) σ (E i)) ∧
      S 0 ⊔ S 1 = tilde Mp ⊤ (commV L) ∧ S 0 ⊓ S 1 = ⊥ := by
  let _i := qAct hB.hD.hyp.Mp_normal
  obtain ⟨n, hpsl, K, hKf, hKfin, hK, I, π, -, hind, hsup, hreal⟩ := h3
  set Z := commV L ⊓ fixV Mp
  set κ := QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hκ
  have hker : ∀ w : W, κ w = 1 ↔ w ∈ fixV Mp := by
    intro w
    rw [hκ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  have hIU : ∀ i, I i ≤ commV L := fun i => hsup ▸ le_sup_of_le_right (le_iSup I i)
  set S : Fin 2 → Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)) := fun i => tilde Mp ⊤ (I i)
  have hSinv : ∀ i, ∀ l : ↥(L.subgroupOf M), ∀ v ∈ S i, l • v ∈ S i := by
    rintro i l _ ⟨u, hu, rfl⟩
    exact ⟨_, (hreal i).2.2.2.1 ⟨((l : ↥M) : MulAut W), Subgroup.mem_subgroupOf.1 l.2⟩ u hu, rfl⟩
  let ψ : ↥L →* ↥(L.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hB.L_le).symm.toMonoidHom
  have hψ : Function.Bijective ψ := (Subgroup.subgroupOfEquivOfLe hB.L_le).symm.bijective
  have hcoord : ∀ i, ∃ E : ↥(S i) ≃* Multiplicative (Fin 2 → K),
      IsNatCoord (L.subgroupOf M) (S i) (ψ.comp π) E := by
    intro i
    let f : ↥(I i) →* ↥(S i) := κ.subgroupMap (I i)
    have hf : Function.Surjective f := κ.subgroupMap_surjective (I i)
    have hfker : ∀ u : ↥(I i), f u = 1 ↔ (u : W) ∈ Z := by
      intro u
      constructor
      · intro h1
        exact ⟨hIU i u.2, (hker u).1 (congrArg Subtype.val h1)⟩
      · intro h1
        exact Subtype.ext ((hker u).2 h1.2)
    have hR := realizesVia_actAut (hSinv i) (hreal i) ψ hψ.2 f hf hfker (fun h u hu => rfl)
    obtain ⟨E, hE⟩ := exists_coord_nat hR
    refine ⟨E, fun γ s s' hss' => ?_⟩
    have h1 := hE γ s
    have h2 : ((((actAut (L.subgroupOf M) (S i) (hSinv i)).rangeRestrict.comp (ψ.comp π)) γ :
        ↥(actAut (L.subgroupOf M) (S i) (hSinv i)).range) : MulAut ↥(S i)) s = s' :=
      Subtype.ext hss'
    subst h2
    exact h1
  choose E hE using hcoord
  have hπ : Function.Bijective π :=
    ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) (hreal 0), (hreal 0).1⟩
  refine ⟨n, K, hKf, hKfin, S, ψ.comp π, E, hpsl, hK, hψ.comp hπ, hSinv, hE, ?_, ?_⟩
  · have hZb : Z.map κ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      exact (hker z).2 hz.2
    calc S 0 ⊔ S 1 = Z.map κ ⊔ ⨆ i, (I i).map κ := by
          rw [hZb, bot_sup_eq]
          refine le_antisymm (sup_le (le_iSup (fun i => (I i).map κ) 0)
            (le_iSup (fun i => (I i).map κ) 1)) (iSup_le fun i => ?_)
          fin_cases i
          · exact le_sup_left
          · exact le_sup_right
      _ = tilde Mp ⊤ (commV L) := by
          rw [← hsup]
          unfold tilde
          rw [Subgroup.map_sup, Subgroup.map_iSup]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    rw [Subgroup.mem_bot]
    have hba : b⁻¹ * a ∈ fixV Mp := by
      rw [← hker, map_mul, map_inv, hab, inv_mul_cancel]
    have hbaU : b⁻¹ * a ∈ commV L :=
      (commV L).mul_mem ((commV L).inv_mem (hIU 1 hb)) (hIU 0 ha)
    have hb1 : b ∈ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      (le_iSup₂ (f := fun (j : Fin 2) (_ : j ≠ 0) => I j) 1 (by decide)) hb
    have hmem : a ∈ Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j := by
      have e : (b⁻¹ * a) * b = a := by rw [mul_comm, mul_inv_cancel_left]
      rw [← e]
      exact Subgroup.mul_mem_sup ⟨hbaU, hba⟩ hb1
    have ha' : a ∈ I 0 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) := ⟨ha, hmem⟩
    rw [hind 0] at ha'
    exact (hker a).2 ha'.2

end Unpack

end CFSG.Quasithin.RonanD321.EndCore
