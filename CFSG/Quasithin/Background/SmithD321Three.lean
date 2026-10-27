module

public import CFSG.Quasithin.Background.SmithD39TwoWit
public import CFSG.Quasithin.Background.SmithD37Out1
public import CFSG.Quasithin.Background.B15P4Res

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
  CFSG.Assembly.LowTwoRank
open scoped Pointwise


section Family

theorem iSup_fin_succ_eq {α : Type*} [CompleteLattice α] {m : ℕ} (f : Fin (m + 1) → α) :
    (⨆ i, f i) = (⨆ i : Fin m, f i.castSucc) ⊔ f (Fin.last m) := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (iSup_le fun i => le_iSup f _) (le_iSup f _))
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact le_sup_right
  · exact le_sup_of_le_left (le_iSup (fun j : Fin m => f j.castSucc) j)

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem rk_biSup_le [Finite Q] {k : ℕ} (S : Fin k → Subgroup Q) {r : ℕ}
    (hS : ∀ i, rk ↥(S i) ≤ r) (s : Finset (Fin k)) :
    rk ↥(⨆ i ∈ s, S i) ≤ s.card * r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (⨆ i ∈ (∅ : Finset (Fin k)), S i) = ⊥ := by
      rw [← Finset.iSup_coe, Finset.coe_empty]
      exact iSup_emptyset
    rw [h0, rk_bot]
    exact Nat.zero_le _
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.card_insert_of_notMem ha]
    have h1 := rk_sup_add_rk_inf (S a) (⨆ i ∈ s, S i)
    have h2 := hS a
    nlinarith

theorem exists_family_of_iSup [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {A : Type*} [Group A]
    [MulDistribMulAction A Q] {I : Subgroup Q} (hI : XMod.IsIrr A I) {ι : Type*}
    (J : ι → Subgroup Q) (hJ : ∀ j, XMod.IsIrr A (J j) ∧ XMod.Iso A (J j) I) {k : ℕ}
    (hk : rk ↥(⨆ j, J j) = k * rk ↥I) :
    ∃ S : Fin k → Subgroup Q, (∀ i, ∃ j, S i = J j) ∧
      (∀ i, S i ⊓ ⨆ (i' : Fin k) (_ : i' ≠ i), S i' = ⊥) ∧ (⨆ i, S i) = ⨆ j, J j := by
  classical
  have hrkI : 0 < rk ↥I := by
    by_contra h0
    exact hI.2.1.ne' ((rk_eq_zero_iff hQ).1 (by omega))
  have hrkJ : ∀ j, rk ↥(J j) = rk ↥I := fun j => by
    obtain ⟨φ, -⟩ := (hJ j).2
    unfold rk
    rw [Nat.card_congr φ.toEquiv]
  have step : ∀ m ≤ k, ∃ S : Fin m → Subgroup Q, (∀ i, ∃ j, S i = J j) ∧
      rk ↥(⨆ i, S i) = m * rk ↥I := by
    intro m
    induction m with
    | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, by rw [iSup_of_empty, rk_bot, zero_mul]⟩
    | succ m ih =>
      intro hm
      obtain ⟨S, hS, hrk⟩ := ih (by omega)
      have hle : (⨆ i, S i) ≤ ⨆ j, J j := iSup_le fun i => by
        obtain ⟨j, hj⟩ := hS i
        rw [hj]
        exact le_iSup J j
      obtain ⟨j, hj⟩ : ∃ j, ¬ J j ≤ ⨆ i, S i := by
        by_contra hcon
        push Not at hcon
        have h2 := rk_mono (iSup_le hcon)
        rw [hk, hrk] at h2
        have := Nat.le_of_mul_le_mul_right h2 hrkI
        omega
      have hinvS : XMod.IsInv A (⨆ i, S i) := XMod.isInv_iSup fun i => by
        obtain ⟨j', hj'⟩ := hS i
        rw [hj']
        exact (hJ j').1.1
      have hinf : J j ⊓ (⨆ i, S i) = ⊥ := by
        rcases (hJ j).1.2.2 _ ((hJ j).1.1.inf hinvS) bot_le inf_le_left with h | h
        · exact h
        · exact absurd (h ▸ inf_le_right) hj
      refine ⟨Fin.snoc S (J j), fun i => ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun i' => ?_) i
        · exact ⟨j, by rw [Fin.snoc_last]⟩
        · rw [Fin.snoc_castSucc]
          exact hS i'
      · have hsup : (⨆ i, (Fin.snoc S (J j) : Fin (m + 1) → Subgroup Q) i) =
            (⨆ i, S i) ⊔ J j := by
          rw [iSup_fin_succ_eq]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [hsup]
        have h1 := rk_sup_add_rk_inf (⨆ i, S i) (J j)
        rw [inf_comm, hinf, rk_bot, hrkJ, hrk] at h1
        rw [add_mul, one_mul]
        omega
  obtain ⟨S, hS, hrk⟩ := step k le_rfl
  have hle : (⨆ i, S i) ≤ ⨆ j, J j := iSup_le fun i => by
    obtain ⟨j, hj⟩ := hS i
    rw [hj]
    exact le_iSup J j
  have hsup : (⨆ i, S i) = ⨆ j, J j := eq_of_le_of_rk_le hQ hle (by rw [hk, hrk])
  have hrkS : ∀ i, rk ↥(S i) = rk ↥I := fun i => by
    obtain ⟨j, hj⟩ := hS i
    rw [hj, hrkJ]
  refine ⟨S, hS, fun i => ?_, hsup⟩
  have hfin : (⨆ (i' : Fin k) (_ : i' ≠ i), S i') = ⨆ i' ∈ (Finset.univ.erase i), S i' := by
    congr 1
    ext i'
    simp [Finset.mem_erase]
  have h1 := rk_biSup_le S (fun i' => (hrkS i').le) (Finset.univ.erase i)
  rw [← hfin, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin] at h1
  have htot : S i ⊔ ⨆ (i' : Fin k) (_ : i' ≠ i), S i' = ⨆ j, J j := by
    refine le_antisymm (sup_le (hsup ▸ le_iSup S i) (iSup₂_le fun i' _ => hsup ▸ le_iSup S i'))
      ?_
    rw [← hsup]
    refine iSup_le fun i' => ?_
    by_cases hii : i' = i
    · rw [hii]; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le i' hii le_rfl)
  have h2 := rk_sup_add_rk_inf (S i) (⨆ (i' : Fin k) (_ : i' ≠ i), S i')
  rw [htot, hk, hrkS i] at h2
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (fun h => by rw [h] at i; exact i.elim0)
  have h3 : (k - 1) * rk ↥I + rk ↥I = k * rk ↥I := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hk1]
  exact (rk_eq_zero_iff hQ).1 (by omega)

end Family


theorem realizesVia_of_secHom {V : Type*} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)}
    {U Z U' Z' : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π)
    (hZU' : Z' ≤ U') (hHU' : ∀ g : ↥H, ∀ u ∈ U', (g : MulAut V) u ∈ U')
    (hHZ' : ∀ g : ↥H, ∀ z ∈ Z', (g : MulAut V) z ∈ Z')
    (ψ : ↥U' →* ↥U ⧸ Z.subgroupOf U) (hψs : Function.Surjective ψ)
    (hψk : ∀ u : ↥U', ψ u = 1 ↔ (u : V) ∈ Z')
    (hψe : ∀ (g : ↥H) (u' : ↥U') (u : ↥U) (hu' : (g : MulAut V) u' ∈ U')
      (hu : (g : MulAut V) u ∈ U), ψ u' = QuotientGroup.mk u →
        ψ ⟨(g : MulAut V) u', hu'⟩ = QuotientGroup.mk ⟨(g : MulAut V) u, hu⟩) :
    D.RealizesVia H U' Z' π := by
  obtain ⟨hπs, hZU, hker, hHU, hHZ, hsec, hkerinv, β, hβs, hβk, hβe⟩ := h
  have hle : Z.subgroupOf U ≤ β.ker := fun u hu => (hβk u).2 hu
  let βb : ↥U ⧸ Z.subgroupOf U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    QuotientGroup.lift (Z.subgroupOf U) β hle
  have hβb : ∀ u : ↥U, βb (QuotientGroup.mk u) = β u := fun u => rfl
  have hβbi : ∀ x, βb x = 1 → x = 1 := by
    intro x hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hβb] at hx
    rw [QuotientGroup.eq_one_iff]
    exact (hβk u).1 hx
  refine ⟨hπs, hZU', hker, hHU', hHZ', hsec, hkerinv, βb.comp ψ, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨u, hu⟩ := hβs q
    obtain ⟨u', hu'⟩ := hψs (QuotientGroup.mk u)
    exact ⟨u', by rw [MonoidHom.comp_apply, hu', hβb, hu]⟩
  · intro u'
    rw [MonoidHom.comp_apply, ← hψk]
    exact ⟨hβbi _, fun h1 => by rw [h1, map_one]⟩
  · intro γ u' m hu'' hm hbu
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (ψ u')
    have hgu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
    have h1 : β u = QuotientGroup.mk m := by
      rw [← hβb, hu]
      exact hbu
    rw [MonoidHom.comp_apply, hψe (π γ) u' u hu'' hgu hu.symm, hβb]
    exact hβe γ u m hgu hm h1




section Copy

variable {W : Type} [CommGroup W] {M Mp L : Subgroup (MulAut W)}

noncomputable def tildeEquiv (V : Subgroup W) :
    ↥(tilde Mp (⊤ : Subgroup W) V) ≃* ↥V ⧸ (V ⊓ fixV Mp).subgroupOf V :=
  ((QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap V)
      ((QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap_surjective V)).symm).trans
    (QuotientGroup.quotientMulEquivOfEq (by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h2 : (QuotientGroup.mk (v : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1 :=
          congrArg Subtype.val h
        rw [QuotientGroup.eq_one_iff, modFix_top_eq] at h2
        exact ⟨v.2, h2⟩
      · intro h
        apply Subtype.ext
        show (QuotientGroup.mk (v : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1
        rw [QuotientGroup.eq_one_iff, modFix_top_eq]
        exact h.2))

theorem tildeEquiv_mk (V : Subgroup W) (v : ↥V) :
    tildeEquiv (Mp := Mp) V ⟨QuotientGroup.mk (v : W), ⟨v, v.2, rfl⟩⟩ = QuotientGroup.mk v := by
  apply (MulEquiv.eq_symm_apply _).1
  rfl

theorem realizesVia_of_iso_tilde (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hLM : L ≤ M) {D : FFModel} {V I : Subgroup W} {π : D.Gam →* ↥L}
    (hR : D.RealizesVia L V (V ⊓ fixV Mp) π) (hIL : ∀ g ∈ L, ∀ u ∈ I, g u ∈ I)
    (hiso : letI := qAct hMp; XMod.Iso ↥(L.subgroupOf M) (tilde Mp ⊤ I) (tilde Mp ⊤ V)) :
    D.RealizesVia L I (I ⊓ fixV Mp) π := by
  let _i := qAct hMp
  obtain ⟨φ, hφ⟩ := hiso
  have hLZ : ∀ g ∈ L, ∀ z ∈ fixV Mp, g z ∈ fixV Mp := by
    intro g hg z hz x hx
    have hgx : g⁻¹ * x * g ∈ Mp := by
      have := (Subgroup.mem_normalizer_iff''.1 (hMp (hLM hg)) x).1 hx
      exact this
    have h1 : (g⁻¹ * x * g) z = z := hz _ hgx
    calc x (g z) = g ((g⁻¹ * x * g) z) := by
          simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      _ = g z := by rw [h1]
  let κ : ↥I →* ↥(tilde Mp (⊤ : Subgroup W) I) :=
    (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap I
  let ψ : ↥I →* ↥V ⧸ (V ⊓ fixV Mp).subgroupOf V :=
    (tildeEquiv V).toMonoidHom.comp (φ.toMonoidHom.comp κ)
  have hψ : ∀ u : ↥I, ψ u = tildeEquiv V (φ (κ u)) := fun u => rfl
  refine realizesVia_of_secHom hR inf_le_left (fun g u hu => hIL g g.2 u hu)
    (fun g z hz => ⟨hIL g g.2 z hz.1, hLZ g g.2 z hz.2⟩) ψ ?_ ?_ ?_
  · exact (tildeEquiv V).surjective.comp (φ.surjective.comp
      ((QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))).subgroupMap_surjective I))
  · intro u
    rw [hψ, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      have h2 : (QuotientGroup.mk (u : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1 :=
        congrArg Subtype.val h
      rw [QuotientGroup.eq_one_iff, modFix_top_eq] at h2
      exact ⟨u.2, h2⟩
    · intro h
      apply Subtype.ext
      show (QuotientGroup.mk (u : W) : W ⧸ modFix Mp (⊤ : Subgroup W)) = 1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq]
      exact h.2
  · intro g u' u hu' hu h
    let ĝ : ↥(L.subgroupOf M) := ⟨⟨g, hLM g.2⟩, Subgroup.mem_subgroupOf.2 g.2⟩
    have hx : φ (κ u') = ⟨QuotientGroup.mk (u : W), ⟨u, u.2, rfl⟩⟩ := by
      apply (tildeEquiv V).injective
      rw [← hψ, h, tildeEquiv_mk]
    have h1 := hφ ĝ (κ u') (κ ⟨(g : MulAut W) u', hu'⟩) rfl
    rw [hx] at h1
    have h2 : φ (κ ⟨(g : MulAut W) u', hu'⟩) =
        ⟨QuotientGroup.mk ((g : MulAut W) u), ⟨(g : MulAut W) u, hu, rfl⟩⟩ :=
      Subtype.ext h1.symm
    rw [hψ, h2]
    exact tildeEquiv_mk V ⟨_, hu⟩

end Copy




section Builder

variable {W : Type} [CommGroup W] {M Mp L : Subgroup (MulAut W)}

theorem directSumOfCopies_of_family (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hLM : L ≤ M) {D : FFModel} {V U : Subgroup W} {π : D.Gam →* ↥L}
    (hR : D.RealizesVia L V (V ⊓ fixV Mp) π) (hUL : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U) {k : ℕ}
    (S : Fin k → Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))
    (hS : letI := qAct hMp; ∀ i, XMod.IsInv ↥(L.subgroupOf M) (S i) ∧
      XMod.Iso ↥(L.subgroupOf M) (S i) (tilde Mp ⊤ V))
    (hind : ∀ i, S i ⊓ ⨆ (j : Fin k) (_ : j ≠ i), S j = ⊥)
    (hsup : (⨆ i, S i) = tilde Mp ⊤ U) :
    DirectSumOfCopies L U (U ⊓ fixV Mp) D k := by
  let _i := qAct hMp
  set κ := QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hκ
  have hker : ∀ w : W, κ w = 1 ↔ w ∈ fixV Mp := by
    intro w
    rw [hκ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  set I : Fin k → Subgroup W := fun i => U ⊓ (S i).comap κ with hI
  have hSU : ∀ i, S i ≤ tilde Mp ⊤ U := fun i => hsup ▸ le_iSup S i
  have hmapI : ∀ i, tilde Mp ⊤ (I i) = S i := by
    intro i
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · obtain ⟨u, hu, rfl⟩ := hSU i hx
      exact ⟨u, ⟨hu, hx⟩, rfl⟩
  have hZI : ∀ i, U ⊓ fixV Mp ≤ I i := fun i z hz =>
    ⟨hz.1, show κ z ∈ S i by rw [(hker z).2 hz.2]; exact (S i).one_mem⟩
  have hIL : ∀ i, ∀ g ∈ L, ∀ u ∈ I i, g u ∈ I i := by
    intro i g hg u hu
    refine ⟨hUL g hg u hu.1, ?_⟩
    have h1 := (hS i).1 ⟨⟨g, hLM hg⟩, Subgroup.mem_subgroupOf.2 hg⟩ (κ u) hu.2
    exact h1
  have hIZ : ∀ i, I i ⊓ fixV Mp = U ⊓ fixV Mp := by
    intro i
    refine le_antisymm (inf_le_inf_right _ inf_le_left) fun z hz => ⟨hZI i hz, hz.2⟩
  have hreal : ∀ i, D.RealizesVia L (I i) (U ⊓ fixV Mp) π := by
    intro i
    have h1 := realizesVia_of_iso_tilde hMp hLM hR (hIL i) (by rw [hmapI i]; exact (hS i).2)
    rwa [hIZ i] at h1
  have hmap_sup : ∀ (s : Set (Fin k)), (⨆ j ∈ s, I j).map κ = ⨆ j ∈ s, S j := by
    intro s
    rw [Subgroup.map_iSup]
    refine iSup_congr fun j => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun _ => hmapI j
  refine ⟨I, π, hZI, fun i => ?_, ?_, hreal⟩
  · refine le_antisymm (fun x hx => ?_) (le_inf (hZI i) le_sup_left)
    obtain ⟨hxI, hxS⟩ := hx
    have h1 : κ x ∈ (U ⊓ fixV Mp ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j).map κ := ⟨x, hxS, rfl⟩
    have h2 : (U ⊓ fixV Mp ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j).map κ ≤
        ⨆ (j : Fin k) (_ : j ≠ i), S j := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        rw [(hker z).2 hz.2]
        exact Subgroup.one_mem _
      · exact (hmap_sup {j | j ≠ i}).le
    have h3 : κ x ∈ S i ⊓ ⨆ (j : Fin k) (_ : j ≠ i), S j := ⟨hxI.2, h2 h1⟩
    rw [hind i, Subgroup.mem_bot, hker] at h3
    exact ⟨hxI.1, h3⟩
  · refine le_antisymm (sup_le inf_le_left (iSup_le fun i => inf_le_left)) fun u hu => ?_
    have h1 : κ u ∈ (⨆ i, I i).map κ := by
      rw [Subgroup.map_iSup]
      have : κ u ∈ tilde Mp ⊤ U := ⟨u, hu, rfl⟩
      rw [← hsup] at this
      refine (iSup_congr fun i => hmapI i).symm ▸ this
    obtain ⟨y, hy, hyu⟩ := h1
    have hyU : y ∈ U := (iSup_le fun i => inf_le_left : (⨆ i, I i) ≤ U) hy
    have hz : y⁻¹ * u ∈ U ⊓ fixV Mp := by
      refine ⟨U.mul_mem (U.inv_mem hyU) hu, (hker _).1 ?_⟩
      rw [map_mul, map_inv, hyu, inv_mul_cancel]
    have : u = y * (y⁻¹ * u) := by group
    rw [this, sup_comm]
    exact Subgroup.mul_mem_sup hy hz

end Builder


section Three

variable {W : Type} [CommGroup W] {M Mp L : Subgroup (MulAut W)}

theorem d321Three_of_family (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hLM : L ≤ M) {V : Subgroup W} (hVZ : V ⊓ fixV L = V ⊓ fixV Mp) {n : ℕ} (hn : 2 ≤ n)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 2 n)
    (S : Fin 2 → Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))
    (hS : letI := qAct hMp; ∀ i, XMod.IsInv ↥(L.subgroupOf M) (S i) ∧
      XMod.Iso ↥(L.subgroupOf M) (S i) (tilde Mp ⊤ V))
    (hind : ∀ i, S i ⊓ ⨆ (j : Fin 2) (_ : j ≠ i), S j = ⊥)
    (hsup : (⨆ i, S i) = tilde Mp ⊤ (commV L)) : D321Three Mp L := by
  obtain ⟨K, hKf, hKfin, hK, e, he⟩ := exists_equiv_of_binaryNaturalSL hnat
  rw [hVZ] at he
  have : CharP K 2 := charP_two_of_card hK
  have : Fintype K := Fintype.ofFinite K
  refine ⟨n, SmithD37.isPSL_of_mulEquiv hn hK e.symm, K, hKf, hKfin, hK, ?_⟩
  exact directSumOfCopies_of_family hMp hLM he
    (fun g hg u hu => B15P4.map_commV_mem (Subgroup.le_normalizer hg) u hu) S hS hind hsup

end Three

end CFSG.Quasithin.SmithD321
