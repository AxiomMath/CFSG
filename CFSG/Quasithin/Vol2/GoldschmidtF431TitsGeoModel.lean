module

public import Certificates.Data.RuF45Geom
public import Certificates.Data.TitsF46Words
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoPtLocThm
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoTransport
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLocLn
public import Certificates.Certificate4190
public import Certificates.Kernel.J4Count.FixCE

public noncomputable section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.RuF45 CFSG.TitsF46
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin.H13.F431.F45

theorem tits_geometry (h : Certificates.titsGeoFacts) :
    ∃ e : titsSetting.ι.Γ ≃ Vtx, e titsSetting.ι.xv = Sum.inl 0 ∧ e titsSetting.ι.lv = Sum.inr 0 ∧
      (∀ (y : ↥titsD) (a : titsSetting.ι.Γ), e (phiD y • a) = y • e a) ∧
      (∀ a b, titsSetting.ι.graph.Adj a b ↔ octGraph.Adj (e a) (e b)) ∧
      PtLoc ↥titsD octGraph (Sum.inl 0) (ofCode 87) (Sum.inr 0) ∧
      (∃ lab : ZMod 5 → Vtx, AffLab ↥titsD octGraph (Sum.inl 0) lab) ∧
      LnLoc ↥titsD octGraph (Sum.inr 0) (ofCode 45) (ofCode 1862) (ofCode 1896) ∧
      IsGenPolygon octGraph 8 := by
  obtain ⟨hPt, ⟨lab, hAff⟩, hLn, hpoly⟩ := h
  have hconn : octGraph.Connected := hpoly.connected
  have h12 : octGraph.Adj (Sum.inl 0) (Sum.inr 0) := hPt.adj
  have f₁ : ∀ b, octGraph.Adj (Sum.inl 0) b →
      ∃ y : ↥titsD, y • (Sum.inl 0 : Vtx) = Sum.inl 0 ∧ y • (Sum.inr 0 : Vtx) = b :=
    fun b hb => (hPt.trans b hb).imp fun k hk => ⟨hk.1, hk.2.2⟩
  have f₂ : ∀ b, octGraph.Adj (Sum.inr 0) b →
      ∃ y : ↥titsD, y • (Sum.inr 0 : Vtx) = Sum.inr 0 ∧ y • (Sum.inl 0 : Vtx) = b :=
    fun b hb => hLn.flag h12.symm hb
  have hcov := cov_of_flags hconn f₁ f₂
  obtain ⟨e, he1, he2, heq, hadj⟩ :=
    (xdatumD (octGraph_adj_inl_inr.1 h12)).exists_equiv hcov f₁
  exact ⟨e, he1, he2, heq, hadj, hPt, ⟨lab, hAff⟩, hLn, hpoly⟩

theorem titsModel_of_check (h : Certificates.titsGeoFacts) :
    TitsModel titsSetting.ι 6 ∧ IsGenPolygon titsSetting.ι.graph 8 := by
  obtain ⟨e, he1, he2, heq, hadj, hPt, ⟨labV, hAff⟩, hLn, hpoly⟩ := tits_geometry h
  have E : EqData phiD e octGraph titsSetting.ι.graph := ⟨phiD_surjective, heq, hadj⟩
  let iso : titsSetting.ι.graph ≃g octGraph := ⟨e, fun {a b} => (hadj a b).symm⟩
  have hpolyι : IsGenPolygon titsSetting.ι.graph 8 := IsGenPolygon.of_iso iso hpoly
  have hPt' : PtLoc titsSetting.ι.G0 titsSetting.ι.graph titsSetting.ι.xv
      (e.symm (ofCode 87)) titsSetting.ι.lv :=
    PtLoc.transport E (by rw [he1, he2, Equiv.apply_symm_apply]; exact hPt)
  have hAff' : AffLab titsSetting.ι.G0 titsSetting.ι.graph titsSetting.ι.xv
      (fun i => e.symm (labV i)) :=
    AffLab.transport E (by rw [he1]; exact hAff)
  have hLn' : LnLoc titsSetting.ι.G0 titsSetting.ι.graph titsSetting.ι.lv
      (e.symm (ofCode 45)) (e.symm (ofCode 1862)) (e.symm (ofCode 1896)) :=
    LnLoc.transport E (by rw [he2]; simpa using hLn)
  have hcard : ∀ u : titsSetting.ι.Γ,
      Nat.card (CosetGeom.nbrs u) = Nat.card (octGraph.neighborSet (e u)) := fun u =>
    Nat.card_congr (e.subtypeEquiv (fun δ => hadj u δ))
  have c1 := RankTwoAmalgam.Completion.nbrs_xv_card (c := titsSetting.ι) titsSetting.hι
  have c2 := RankTwoAmalgam.Completion.nbrs_lv_card (c := titsSetting.ι) titsSetting.hι
  have n1 : Nat.card (octGraph.neighborSet (Sum.inl 0)) = 5 := by
    have : Nat.card (ZMod 5) = Nat.card (octGraph.neighborSet (Sum.inl 0)) :=
      Nat.card_congr (Equiv.ofBijective
        (fun i : ZMod 5 => (⟨labV i, hAff.adj i⟩ : octGraph.neighborSet (Sum.inl 0)))
        ⟨fun i j hij => hAff.inj (congrArg Subtype.val hij), fun ⟨u, hu⟩ => by
          obtain ⟨i, hi⟩ := hAff.surj u hu
          exact ⟨i, Subtype.ext hi⟩⟩)
    rw [← this]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have n2 : Nat.card (octGraph.neighborSet (Sum.inr 0)) = 3 := by
    rw [Nat.card_coe_set_eq]
    exact hLn.card
  refine ⟨⟨titsSetting.hι, ?_, ?_, by norm_num, by decide, ?_, ?_, ?_, ?_, ?_⟩, hpolyι⟩
  · unfold RankTwoAmalgam.qOne
    rw [← c1, hcard, he1, n1]
    norm_num
  · unfold RankTwoAmalgam.qTwo
    rw [← c2, hcard, he2, n2]
  · exact fun q q' hq hq' => hPt'.pathTrans hpolyι hq hq'
  · exact fun q q' hq hq' => hLn'.pathTrans7 hpolyι hq hq'
  · exact fun p hp y hy hne => hPt'.noFix hpolyι hp hy hne
  · exact fun p hp q hq hpq y y' hy hy' => hPt'.transPair hpolyι hAff' hp hq hpq hy hy'
  · exact fun p hp q hq hpq y y' hy hy' => hLn'.transPair hpolyι hp hq hpq hy hy'

end CFSG.Quasithin.TitsGeo
